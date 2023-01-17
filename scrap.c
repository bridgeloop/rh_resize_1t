/*
	ISC License
	
	Copyright (c) 2022, aiden (aiden@cmp.bz)
	
	Permission to use, copy, modify, and/or distribute this software for any
	purpose with or without fee is hereby granted, provided that the above
	copyright notice and this permission notice appear in all copies.
	
	THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
	WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
	MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
	ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
	WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
	ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
	OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*/

static void s_hashmap_resize(struct hashmap *hashmap, struct hashmap_area *area, bool is_main_thread) {
	/*
		this relies on the fact that the buckets' hashes (mod hashmap->n_buckets) are
		already sequential from a particular index onwards. all of the buckets' hashes
		(mod hashmap->n_buckets * multiplier) will be sequential from a particular index
		onwards after this resize algorithm completes.

		SEQUENTIAL (mod hashmap->n_buckets) FROM A TO B
		current layout:

			[wrapping buckets 1] B A <buckets 1>

		assuming multiplier == 2
		SEQUENTIAL (mod hashmap->n_buckets * 2) FROM A TO B
		next layout:

			[wrapping buckets 2] B A <buckets 1> [some of the previously wrapping buckets] <buckets 2>

		this works because each bucket's hash (mod hashmap->n_buckets * multiplier)
		is guaranteed to be itself plus a multiple of hashmap->n_buckets (including 0).

		this might result in mediocre element distribution post-resize.
	*/
	if (hashmap->resize_fail) {
		return;
	}

	area->lock = false;

	if (!is_main_thread) {
		// should resize, but there is
		// already a thread trying to resize.
		pthread_mutex_lock(&(hashmap->resize_mutex));
		pthread_cond_signal(&(hashmap->resize_cond));
		pthread_mutex_unlock(&(hashmap->resize_mutex));
		pthread_mutex_lock(&(hashmap->ensured_mutex));
		while (hashmap->resizing) {
			pthread_cond_wait(&(hashmap->ensured_cond), &(hashmap->ensured_mutex));
		}
		pthread_mutex_unlock(&(hashmap->ensured_mutex));
		area->lock = true;
		return;
	}

	// thread that acquired "resizing"
	pthread_mutex_lock(&(hashmap->resize_mutex));
	wait:;
	// wait for other threads to stop working
	ifc_iter(struct hashmap_area)(hashmap->ifc, it_area) {
		if (it_area->lock) {
			pthread_cond_wait(&(hashmap->resize_cond), &(hashmap->resize_mutex));
			goto wait;
		}
	}
	pthread_mutex_unlock(&(hashmap->resize_mutex));

	area->lock = true;

	uint32_t multiplier;

	uint32_t least = hashmap->resize_least;
	if (least < hashmap->n_buckets * 2) {
		least = hashmap->n_buckets * 2;
	}
	least *= 1.05;

	float div_f32 = (float)least / (float)hashmap->n_buckets;
	uint32_t div_u32 = least / hashmap->n_buckets;
	if ((uint32_t)div_f32 == div_u32) {
		multiplier = div_u32;
	} else {
		multiplier = div_u32 + 1;
	}

	uint32_t next_buckets;
	struct hashmap_bucket *buckets;
	if (__builtin_mul_overflow(hashmap->n_buckets, multiplier, &(next_buckets))) {
		// multiplication overflow
		buckets = NULL;
	} else {
		// allocate new buckets array
		buckets = malloc(next_buckets * sizeof(struct hashmap_bucket));
	}

	if (buckets == NULL) {
		hashmap->resize_fail = true;
		__atomic_clear(&(hashmap->resizing), __ATOMIC_RELEASE);
		pthread_mutex_lock(&(hashmap->ensured_mutex));
		pthread_cond_broadcast(&(hashmap->ensured_cond));
		pthread_mutex_unlock(&(hashmap->ensured_mutex));
		return;
	}

	struct mltpl_ctx {
		uint8_t init;

		uint32_t lseen, rseen, rseq;
		uint32_t lreq, rgap;

		uint32_t n_wrapping;

		void *head, *tail;
	};
	struct mltpl_ctx ctxs[multiplier];
	for (size_t idx = 0; idx < multiplier; ++idx) {
		ctxs[idx].init = 0;
		ctxs[idx].n_wrapping = 0;

		ctxs[idx].head = ctxs[idx].tail = NULL;
	}

	uint32_t base = 0;
	uint32_t running = 0;
	while (
		hashmap->buckets[base].protected.kv != NULL &&
		hashmap->buckets[base].protected.psl > base
	) {
		size_t pos = hashmap->buckets[base].protected.hash % next_buckets;
		struct mltpl_ctx *ctx = &(ctxs[pos / hashmap->n_buckets]);

		ctx->n_wrapping += 1;

		void **node = ((void **)buckets) + base;
		*node = NULL;

		if (ctx->head == NULL) {
			ctx->head = (void *)node;
			running += 1;
		} else {
			*((void **)(ctx->tail)) = (void *)node;
		}
		ctx->tail = (void *)node;

		base += 1;
	}

	uint32_t left_idx = hashmap->n_buckets;

	while (running) {
		uint32_t pos;
		struct mltpl_ctx *ctx;

		if (hashmap->buckets[--left_idx].protected.kv != NULL) {
			pos = hashmap->buckets[left_idx].protected.hash % next_buckets;
			ctx = &(ctxs[pos / hashmap->n_buckets]);
		} else {
			ctx = NULL;
		}

		for (size_t ctx_idx = 0; ctx_idx < multiplier; ++ctx_idx) {
			struct mltpl_ctx *curr_ctx = &(ctxs[ctx_idx]);
			if (
				curr_ctx->n_wrapping == 0 ||
				(curr_ctx->init && (!curr_ctx->lreq || !curr_ctx->rgap))
			) {
				continue;
			}
			if (curr_ctx == ctx) {
				if (!ctx->init) {
					ctx->init = 1;

					ctx->lreq = ctx->rgap =
						(hashmap->n_buckets * (ctx_idx + 1)) - pos - 1;

					ctx->lseen = ctx->rseen =
						pos;
					ctx->rseq = 1;

					if (!ctx->lreq || !ctx->rgap) {
						running -= 1;
					}
					continue;
				}
				if (pos == ctx->lseen) {
					if (ctx->lreq == ctx->rgap) {
						ctx->rgap -= 1;
						ctx->rseq += 1;
					}
					ctx->lreq -= 1;
					if (!ctx->lreq || !ctx->rgap) {
						running -= 1;
					}
				} else {
					assert(!(pos > ctx->lseen));
					ctx->lreq += ctx->lseen - pos - 1;
					ctx->lseen = pos;
				}
			} else {
				void **head = (void **)curr_ctx->head;
				curr_ctx->head = *head;
				curr_ctx->n_wrapping -= 1;
				uint32_t bucket_idx =
					(uint32_t)(head - (void **)buckets);
				uint32_t pos =
					hashmap->buckets[bucket_idx].protected.hash % next_buckets;
				assert(pos < (hashmap->n_buckets * (ctx_idx + 1)));
				if (!curr_ctx->init) {
					curr_ctx->init = 1;

					curr_ctx->lreq = curr_ctx->rgap =
						(hashmap->n_buckets * (ctx_idx + 1)) - pos - 1;

					curr_ctx->lseen = curr_ctx->rseen =
						pos;
					curr_ctx->rseq = 1;
					if (*head == NULL || (!curr_ctx->lreq || !curr_ctx->rgap)) {
						running -= 1;
					}
					continue;
				}
				if (curr_ctx->rseen + curr_ctx->rseq >= pos) {
					curr_ctx->rgap -= 1;
					curr_ctx->rseq += 1;
					curr_ctx->lreq -= 1;
				} else {
					curr_ctx->rseen = pos;
					curr_ctx->rseq = 1;
					curr_ctx->rgap = (hashmap->n_buckets * (ctx_idx + 1)) - pos - 1;
					curr_ctx->lreq -= 1;
				}
				if ((!curr_ctx->lreq || !curr_ctx->rgap) || *head == NULL) {
					running -= 1;
				}
			}
		}
	}

	// copy the buckets over //

	// this fills in angle-bracket fields at the same time,
	// then square-bracket fields at the same time if required

	struct frag_ctx {
		uint64_t idx, sentinel;
	};
	struct frag_ctx fragments[multiplier];

	fragments[0].idx = ctxs[multiplier - 1].n_wrapping;
	fragments[0].sentinel = hashmap->n_buckets + ctxs[0].n_wrapping;
	for (uint32_t idx = 1; idx < multiplier; ++idx) {
		fragments[idx].idx = fragments[idx - 1].sentinel;
		fragments[idx].sentinel = (hashmap->n_buckets * (idx + 1)) + ctxs[idx].n_wrapping;
	}

	for (uint32_t it = 0; it < hashmap->n_buckets; ++it) {
		uint32_t idx = base + it;
		if (idx >= hashmap->n_buckets) {
			idx -= hashmap->n_buckets;
		}

		struct hashmap_bucket *bkt = &(hashmap->buckets[idx]);
		struct hashmap_bucket_protected *prot = &(bkt->protected);

		if (prot->kv == NULL) {
			continue;
		}

		uint32_t new_bkt = prot->hash % next_buckets;
		struct frag_ctx *frag = &(fragments[new_bkt / hashmap->n_buckets]);

		uint64_t bkt_idx;
		if (frag->idx < next_buckets) {
			for (; frag->idx < new_bkt; ++(frag->idx)) {
				buckets[frag->idx].protected.kv = NULL;
				__atomic_clear(&(buckets[frag->idx].lock), __ATOMIC_RELAXED);
			}
			bkt_idx = frag->idx;
		} else {
			bkt_idx = frag->idx - next_buckets;
		}

		prot->psl = frag->idx - new_bkt;
		buckets[bkt_idx].protected = *prot;
		__atomic_clear(&(buckets[bkt_idx].lock), __ATOMIC_RELAXED);

		frag->idx += 1;
	}

	for (uint32_t idx = 0; idx < multiplier; ++idx) {
		if (fragments[idx].sentinel == hashmap->n_buckets * (idx + 1)) {
			for (; fragments[idx].idx < fragments[idx].sentinel; ++fragments[idx].idx) {
				buckets[fragments[idx].idx].protected.kv = NULL;
				__atomic_clear(&(buckets[fragments[idx].idx].lock), __ATOMIC_RELAXED);
			}
		}
	}

	free(hashmap->buckets);
	hashmap->buckets = buckets;
	hashmap->n_buckets = next_buckets;

	__atomic_clear(&(hashmap->resizing), __ATOMIC_SEQ_CST);
	pthread_mutex_lock(&(hashmap->ensured_mutex));
	pthread_cond_broadcast(&(hashmap->ensured_cond));
	pthread_mutex_unlock(&(hashmap->ensured_mutex));

	return;
}