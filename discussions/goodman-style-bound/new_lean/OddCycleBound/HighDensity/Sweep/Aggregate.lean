/-
# `eq:constant-A` finite sweep — aggregate dispatch  (GENERATED; do not hand-edit)

Bundles every per-m lemma `constA_m<m>` into the single `constA_finite`: for odd `m` in
`[63, 499]` and every admissible case-A pair, `1 <= gRatA m r`.  `constA_finite_B0` then
lifts it to `eq:constant-A` in `B0` form (matching `constA_m500`) via `constA_of_gRatA`.
-/

import OddCycleBound.HighDensity.Sweep.M063
import OddCycleBound.HighDensity.Sweep.M065
import OddCycleBound.HighDensity.Sweep.M067
import OddCycleBound.HighDensity.Sweep.M069
import OddCycleBound.HighDensity.Sweep.M071
import OddCycleBound.HighDensity.Sweep.M073
import OddCycleBound.HighDensity.Sweep.M075
import OddCycleBound.HighDensity.Sweep.M077
import OddCycleBound.HighDensity.Sweep.M079
import OddCycleBound.HighDensity.Sweep.M081
import OddCycleBound.HighDensity.Sweep.M083
import OddCycleBound.HighDensity.Sweep.M085
import OddCycleBound.HighDensity.Sweep.M087
import OddCycleBound.HighDensity.Sweep.M089
import OddCycleBound.HighDensity.Sweep.M091
import OddCycleBound.HighDensity.Sweep.M093
import OddCycleBound.HighDensity.Sweep.M095
import OddCycleBound.HighDensity.Sweep.M097
import OddCycleBound.HighDensity.Sweep.M099
import OddCycleBound.HighDensity.Sweep.M101
import OddCycleBound.HighDensity.Sweep.M103
import OddCycleBound.HighDensity.Sweep.M105
import OddCycleBound.HighDensity.Sweep.M107
import OddCycleBound.HighDensity.Sweep.M109
import OddCycleBound.HighDensity.Sweep.M111
import OddCycleBound.HighDensity.Sweep.M113
import OddCycleBound.HighDensity.Sweep.M115
import OddCycleBound.HighDensity.Sweep.M117
import OddCycleBound.HighDensity.Sweep.M119
import OddCycleBound.HighDensity.Sweep.M121
import OddCycleBound.HighDensity.Sweep.M123
import OddCycleBound.HighDensity.Sweep.M125
import OddCycleBound.HighDensity.Sweep.M127
import OddCycleBound.HighDensity.Sweep.M129
import OddCycleBound.HighDensity.Sweep.M131
import OddCycleBound.HighDensity.Sweep.M133
import OddCycleBound.HighDensity.Sweep.M135
import OddCycleBound.HighDensity.Sweep.M137
import OddCycleBound.HighDensity.Sweep.M139
import OddCycleBound.HighDensity.Sweep.M141
import OddCycleBound.HighDensity.Sweep.M143
import OddCycleBound.HighDensity.Sweep.M145
import OddCycleBound.HighDensity.Sweep.M147
import OddCycleBound.HighDensity.Sweep.M149
import OddCycleBound.HighDensity.Sweep.M151
import OddCycleBound.HighDensity.Sweep.M153
import OddCycleBound.HighDensity.Sweep.M155
import OddCycleBound.HighDensity.Sweep.M157
import OddCycleBound.HighDensity.Sweep.M159
import OddCycleBound.HighDensity.Sweep.M161
import OddCycleBound.HighDensity.Sweep.M163
import OddCycleBound.HighDensity.Sweep.M165
import OddCycleBound.HighDensity.Sweep.M167
import OddCycleBound.HighDensity.Sweep.M169
import OddCycleBound.HighDensity.Sweep.M171
import OddCycleBound.HighDensity.Sweep.M173
import OddCycleBound.HighDensity.Sweep.M175
import OddCycleBound.HighDensity.Sweep.M177
import OddCycleBound.HighDensity.Sweep.M179
import OddCycleBound.HighDensity.Sweep.M181
import OddCycleBound.HighDensity.Sweep.M183
import OddCycleBound.HighDensity.Sweep.M185
import OddCycleBound.HighDensity.Sweep.M187
import OddCycleBound.HighDensity.Sweep.M189
import OddCycleBound.HighDensity.Sweep.M191
import OddCycleBound.HighDensity.Sweep.M193
import OddCycleBound.HighDensity.Sweep.M195
import OddCycleBound.HighDensity.Sweep.M197
import OddCycleBound.HighDensity.Sweep.M199
import OddCycleBound.HighDensity.Sweep.M201
import OddCycleBound.HighDensity.Sweep.M203
import OddCycleBound.HighDensity.Sweep.M205
import OddCycleBound.HighDensity.Sweep.M207
import OddCycleBound.HighDensity.Sweep.M209
import OddCycleBound.HighDensity.Sweep.M211
import OddCycleBound.HighDensity.Sweep.M213
import OddCycleBound.HighDensity.Sweep.M215
import OddCycleBound.HighDensity.Sweep.M217
import OddCycleBound.HighDensity.Sweep.M219
import OddCycleBound.HighDensity.Sweep.M221
import OddCycleBound.HighDensity.Sweep.M223
import OddCycleBound.HighDensity.Sweep.M225
import OddCycleBound.HighDensity.Sweep.M227
import OddCycleBound.HighDensity.Sweep.M229
import OddCycleBound.HighDensity.Sweep.M231
import OddCycleBound.HighDensity.Sweep.M233
import OddCycleBound.HighDensity.Sweep.M235
import OddCycleBound.HighDensity.Sweep.M237
import OddCycleBound.HighDensity.Sweep.M239
import OddCycleBound.HighDensity.Sweep.M241
import OddCycleBound.HighDensity.Sweep.M243
import OddCycleBound.HighDensity.Sweep.M245
import OddCycleBound.HighDensity.Sweep.M247
import OddCycleBound.HighDensity.Sweep.M249
import OddCycleBound.HighDensity.Sweep.M251
import OddCycleBound.HighDensity.Sweep.M253
import OddCycleBound.HighDensity.Sweep.M255
import OddCycleBound.HighDensity.Sweep.M257
import OddCycleBound.HighDensity.Sweep.M259
import OddCycleBound.HighDensity.Sweep.M261
import OddCycleBound.HighDensity.Sweep.M263
import OddCycleBound.HighDensity.Sweep.M265
import OddCycleBound.HighDensity.Sweep.M267
import OddCycleBound.HighDensity.Sweep.M269
import OddCycleBound.HighDensity.Sweep.M271
import OddCycleBound.HighDensity.Sweep.M273
import OddCycleBound.HighDensity.Sweep.M275
import OddCycleBound.HighDensity.Sweep.M277
import OddCycleBound.HighDensity.Sweep.M279
import OddCycleBound.HighDensity.Sweep.M281
import OddCycleBound.HighDensity.Sweep.M283
import OddCycleBound.HighDensity.Sweep.M285
import OddCycleBound.HighDensity.Sweep.M287
import OddCycleBound.HighDensity.Sweep.M289
import OddCycleBound.HighDensity.Sweep.M291
import OddCycleBound.HighDensity.Sweep.M293
import OddCycleBound.HighDensity.Sweep.M295
import OddCycleBound.HighDensity.Sweep.M297
import OddCycleBound.HighDensity.Sweep.M299
import OddCycleBound.HighDensity.Sweep.M301
import OddCycleBound.HighDensity.Sweep.M303
import OddCycleBound.HighDensity.Sweep.M305
import OddCycleBound.HighDensity.Sweep.M307
import OddCycleBound.HighDensity.Sweep.M309
import OddCycleBound.HighDensity.Sweep.M311
import OddCycleBound.HighDensity.Sweep.M313
import OddCycleBound.HighDensity.Sweep.M315
import OddCycleBound.HighDensity.Sweep.M317
import OddCycleBound.HighDensity.Sweep.M319
import OddCycleBound.HighDensity.Sweep.M321
import OddCycleBound.HighDensity.Sweep.M323
import OddCycleBound.HighDensity.Sweep.M325
import OddCycleBound.HighDensity.Sweep.M327
import OddCycleBound.HighDensity.Sweep.M329
import OddCycleBound.HighDensity.Sweep.M331
import OddCycleBound.HighDensity.Sweep.M333
import OddCycleBound.HighDensity.Sweep.M335
import OddCycleBound.HighDensity.Sweep.M337
import OddCycleBound.HighDensity.Sweep.M339
import OddCycleBound.HighDensity.Sweep.M341
import OddCycleBound.HighDensity.Sweep.M343
import OddCycleBound.HighDensity.Sweep.M345
import OddCycleBound.HighDensity.Sweep.M347
import OddCycleBound.HighDensity.Sweep.M349
import OddCycleBound.HighDensity.Sweep.M351
import OddCycleBound.HighDensity.Sweep.M353
import OddCycleBound.HighDensity.Sweep.M355
import OddCycleBound.HighDensity.Sweep.M357
import OddCycleBound.HighDensity.Sweep.M359
import OddCycleBound.HighDensity.Sweep.M361
import OddCycleBound.HighDensity.Sweep.M363
import OddCycleBound.HighDensity.Sweep.M365
import OddCycleBound.HighDensity.Sweep.M367
import OddCycleBound.HighDensity.Sweep.M369
import OddCycleBound.HighDensity.Sweep.M371
import OddCycleBound.HighDensity.Sweep.M373
import OddCycleBound.HighDensity.Sweep.M375
import OddCycleBound.HighDensity.Sweep.M377
import OddCycleBound.HighDensity.Sweep.M379
import OddCycleBound.HighDensity.Sweep.M381
import OddCycleBound.HighDensity.Sweep.M383
import OddCycleBound.HighDensity.Sweep.M385
import OddCycleBound.HighDensity.Sweep.M387
import OddCycleBound.HighDensity.Sweep.M389
import OddCycleBound.HighDensity.Sweep.M391
import OddCycleBound.HighDensity.Sweep.M393
import OddCycleBound.HighDensity.Sweep.M395
import OddCycleBound.HighDensity.Sweep.M397
import OddCycleBound.HighDensity.Sweep.M399
import OddCycleBound.HighDensity.Sweep.M401
import OddCycleBound.HighDensity.Sweep.M403
import OddCycleBound.HighDensity.Sweep.M405
import OddCycleBound.HighDensity.Sweep.M407
import OddCycleBound.HighDensity.Sweep.M409
import OddCycleBound.HighDensity.Sweep.M411
import OddCycleBound.HighDensity.Sweep.M413
import OddCycleBound.HighDensity.Sweep.M415
import OddCycleBound.HighDensity.Sweep.M417
import OddCycleBound.HighDensity.Sweep.M419
import OddCycleBound.HighDensity.Sweep.M421
import OddCycleBound.HighDensity.Sweep.M423
import OddCycleBound.HighDensity.Sweep.M425
import OddCycleBound.HighDensity.Sweep.M427
import OddCycleBound.HighDensity.Sweep.M429
import OddCycleBound.HighDensity.Sweep.M431
import OddCycleBound.HighDensity.Sweep.M433
import OddCycleBound.HighDensity.Sweep.M435
import OddCycleBound.HighDensity.Sweep.M437
import OddCycleBound.HighDensity.Sweep.M439
import OddCycleBound.HighDensity.Sweep.M441
import OddCycleBound.HighDensity.Sweep.M443
import OddCycleBound.HighDensity.Sweep.M445
import OddCycleBound.HighDensity.Sweep.M447
import OddCycleBound.HighDensity.Sweep.M449
import OddCycleBound.HighDensity.Sweep.M451
import OddCycleBound.HighDensity.Sweep.M453
import OddCycleBound.HighDensity.Sweep.M455
import OddCycleBound.HighDensity.Sweep.M457
import OddCycleBound.HighDensity.Sweep.M459
import OddCycleBound.HighDensity.Sweep.M461
import OddCycleBound.HighDensity.Sweep.M463
import OddCycleBound.HighDensity.Sweep.M465
import OddCycleBound.HighDensity.Sweep.M467
import OddCycleBound.HighDensity.Sweep.M469
import OddCycleBound.HighDensity.Sweep.M471
import OddCycleBound.HighDensity.Sweep.M473
import OddCycleBound.HighDensity.Sweep.M475
import OddCycleBound.HighDensity.Sweep.M477
import OddCycleBound.HighDensity.Sweep.M479
import OddCycleBound.HighDensity.Sweep.M481
import OddCycleBound.HighDensity.Sweep.M483
import OddCycleBound.HighDensity.Sweep.M485
import OddCycleBound.HighDensity.Sweep.M487
import OddCycleBound.HighDensity.Sweep.M489
import OddCycleBound.HighDensity.Sweep.M491
import OddCycleBound.HighDensity.Sweep.M493
import OddCycleBound.HighDensity.Sweep.M495
import OddCycleBound.HighDensity.Sweep.M497
import OddCycleBound.HighDensity.Sweep.M499

namespace OddCycleBound.HighDensity

/-- **`eq:constant-A` finite sweep, rational form.**  For odd `m` in `[63, 499]`, `2 ≤ r`,
`6r < m` (`θ = r/m ≤ 1/6`), the collapsed rational target satisfies `1 ≤ gRatA m r`. -/
theorem constA_finite {m r : ℕ} (hodd : m % 2 = 1) (hm63 : 63 ≤ m) (hm499 : m ≤ 499)
    (hr2 : 2 ≤ r) (h6r : 6 * r < m) : 1 ≤ gRatA m r := by
  interval_cases m
  · exact constA_m63 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m65 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m67 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m69 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m71 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m73 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m75 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m77 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m79 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m81 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m83 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m85 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m87 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m89 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m91 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m93 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m95 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m97 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m99 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m101 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m103 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m105 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m107 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m109 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m111 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m113 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m115 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m117 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m119 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m121 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m123 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m125 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m127 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m129 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m131 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m133 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m135 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m137 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m139 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m141 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m143 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m145 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m147 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m149 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m151 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m153 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m155 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m157 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m159 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m161 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m163 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m165 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m167 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m169 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m171 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m173 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m175 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m177 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m179 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m181 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m183 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m185 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m187 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m189 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m191 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m193 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m195 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m197 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m199 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m201 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m203 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m205 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m207 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m209 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m211 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m213 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m215 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m217 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m219 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m221 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m223 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m225 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m227 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m229 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m231 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m233 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m235 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m237 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m239 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m241 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m243 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m245 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m247 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m249 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m251 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m253 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m255 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m257 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m259 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m261 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m263 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m265 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m267 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m269 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m271 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m273 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m275 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m277 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m279 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m281 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m283 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m285 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m287 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m289 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m291 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m293 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m295 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m297 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m299 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m301 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m303 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m305 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m307 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m309 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m311 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m313 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m315 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m317 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m319 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m321 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m323 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m325 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m327 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m329 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m331 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m333 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m335 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m337 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m339 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m341 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m343 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m345 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m347 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m349 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m351 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m353 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m355 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m357 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m359 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m361 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m363 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m365 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m367 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m369 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m371 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m373 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m375 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m377 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m379 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m381 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m383 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m385 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m387 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m389 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m391 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m393 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m395 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m397 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m399 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m401 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m403 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m405 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m407 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m409 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m411 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m413 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m415 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m417 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m419 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m421 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m423 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m425 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m427 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m429 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m431 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m433 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m435 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m437 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m439 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m441 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m443 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m445 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m447 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m449 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m451 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m453 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m455 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m457 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m459 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m461 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m463 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m465 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m467 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m469 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m471 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m473 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m475 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m477 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m479 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m481 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m483 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m485 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m487 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m489 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m491 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m493 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m495 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m497 hr2 h6r
  · exact absurd hodd (by decide)
  · exact constA_m499 hr2 h6r

/-- **`eq:constant-A` finite sweep, `B₀` form** (matches `constA_m500`).  For odd `m` in
`[63, 499]` and every admissible case-A pair, `(99/(100m))·P(θ)·B₀(θ)^m ≥ 1`. -/
theorem constA_finite_B0 {m r : ℕ} (hodd : m % 2 = 1) (hm63 : 63 ≤ m) (hm499 : m ≤ 499)
    (hr2 : 2 ≤ r) (h6r : 6 * r < m) :
    1 ≤ 99 / (100 * (m : ℝ))
        * ((2 / 3 - 2 * ((r : ℝ) / m)) / (((r : ℝ) / m) * (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2))
        * (B0 ((r : ℝ) / m)) ^ m :=
  constA_of_gRatA (by omega) h6r (constA_finite hodd hm63 hm499 hr2 h6r)

end OddCycleBound.HighDensity
