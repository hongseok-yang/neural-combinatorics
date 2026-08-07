# Revision style for `paper_new_region2_v2.tex`

Preferences expressed by the author (TaeYoung Kim) during the August 2026 revision pass over
§§1–4. Written for whoever — human or AI — revises this manuscript next. Rules are ordered by how
often they came up, not by importance. Companion file: `TERMINOLOGY.md` (naming of lemmas and
concepts).

## 1. Words that were rejected outright

Never use these:

| Rejected | Use instead | Reason given |
|---|---|---|
| "record" ("we record the identity") | just state it | filler |
| "display" ("the display above") | name the object: "the expansion (4.21)", "the inner integral" | filler |
| "estimated" | "bounded", "derived", "shown nonnegative" | reads as statistics |
| "acts on" (an operator acting on a space) | "is determined by its restriction to", "for `f ∈ E_0`" | suggests group action / mean-field action |
| "read off", "reads off" | "the coefficients are", "we obtain" | — |
| "recording" ("the exponent recording the length") | "the exponent of `z` is the length" | — |
| "budget" (noun, for an inequality) | "the Hilbert–Schmidt bound", "the bound (3.6)" | not a mathematical term |
| "limits of integration" | "endpoints of integration" | collides with `lim`; "bounds" also collides with the paper's many bounds |
| "genuinely", "manifestly", "artificial", "decisive" | delete | rhetoric |
| "the bracket" (for a random variable being averaged) | name it: "the random variable `X^n ρ(u)`" | — |
| "data" ("the same three pieces of data") | "quantities", "notation" | not data |
| "structural facts" | "two elementary lemmas" | — |
| "principal chain", "defect" | describe the actual quantity | jargon the author is removing |

Also rejected as over-precise or unnecessary: "Huber-type envelope" (just define `ψ`), "kernel" for
`(ℓ+s)^{-m}` in the Laplace step, "compression" for `A` (see §5 below).

Grammar slips the author asked to be watched: "equals to" → "equals"; sentences ending "…, the
last step because …" (make it a clause with a verb).

## 2. Show the computation, do not describe it

The single most repeated request. Prose that narrates algebra should be replaced by displayed
algebra.

- "comparison of coefficients with the beta moments shows (4.26)" → expand both sides, give the
  beta moments, and say which factorials cancel.
- "Indeed, expand the power and use …" → write `S^j = Σ (j!/α!)ΘᵅλᵅΘ`, then the Dirichlet moments,
  then the cancellation, as three displays.
- "gamma integration by parts gives" → name the Stein identity and apply it to `f(y)=(y-b)^k`.
- If a step is "immediate", still give the one line that makes it immediate.

Corollary: intermediate steps that make a formula legible must not be dropped
(e.g. keep `2 Σ_{2j≤n} C(n,2j)(1/2)^{n-2j} v^{2j}` between the binomial expansion and `Σ a_j v^{2j}`).

## 3. Order of exposition

- **No forward use.** Never use a symbol before it is defined, even one display earlier. If a
  display needs `L_±`, write `L_±` out in full there and name it afterwards.
- **Observation → conclusion.** State the fact ("the three terms have degree `n` in `(V,W,X)`, and
  `V+W=X`") before the move it justifies. Do not announce a target first ("To reach (4.29), put
  …") — that reads as fitting the strategy to a known answer.
- **Define symbols where they are used.** `X ~ Beta(r,r)`, `ρ_{n,m}`, `n = m−2r` were all moved out
  of the section preamble into the lemma statement that uses them. A symbol used only inside one
  proof belongs inside that proof (`V_X`, `W_X`).
- **Introduce related symbols together**, in one display, when they arrive for the same reason
  (`v = q+xY−1/2 = xY−δ = δ(zY−1)` with `δ` and `z` defined alongside).
- **Restate** a lemma at the top of the section that proves it, so the reader need not page back.
- **One-sentence bridge** between subsections: "To prove that …, we use the following lemma."

## 4. References and numbering

- Equations are numbered by section (`\numberwithin{equation}{section}`).
- Cite as **name + number**: "the moment identity \eqref{eq:dense-dirichlet-moment}", "the
  splitting identity \eqref{eq:dense-h-split}". Never a bare number, and never a name with the
  number dropped.
- Use `align`/`align*` with `\nonumber`, not `equation`+`aligned` (the number should sit on the
  line it labels).
- Cross-references must point at what is actually being used — the author checks. A citation to a
  result that does not contain the quoted form is a bug.
- Background citations go **after** the proof they relate to, not before the statement.
  Delete citations nothing depends on (Simon's *Trace Ideals* was removed for this reason).

## 5. Mathematical care the author checks

- **Terminology must be literally correct.** `A = P T_U P` is a compression, not a restriction of
  `T_U`; when the author asked for "restriction", the qualifying clause `⟨f,Ah⟩ = ⟨f,T_U h⟩ for
  `f,h ⊥ 1`` was added to keep the sentence true.
- **State the weakest sufficient claim.** `H(b_*) ≥ 0` is what the contradiction needs, even
  though the proof yields `> 0`.
- **No redundant parameters.** Prefer `z = x/δ` (one parameter) to `(x,δ)` (scale-redundant); do
  not rename `b := b_*`, just write `b_*`.
- **Do not overstate.** "such a term is nonnegative only if …" became "what is needed is …". Claims
  of sharpness are scoped to the argument ("the exact limit of this argument"), not to the theorem.
- **Factorials over Gamma functions** in explicit constant computations.
- If a claim in the text is **false**, say so and fix it rather than paraphrasing it. Two found
  this pass: "ρ fails to be positive for large `s`" (it is positive for large `s`; the failure is
  in an intermediate window), and `Γ(2r) = (2n−1)!`.

## 6. Case analysis

When the argument splits, make the split visible: a nested `itemize` of the cases with the lemma
that settles each, rather than a narrative. Keep the conditions in the same variables throughout
(the author asked to eliminate `N = m−2` from the map and write everything in `m`).

## 7. Working process

- **Expand first, trim second.** When a passage is unclear the author asks for a longer version,
  reads it, then says what to cut. Do not pre-emptively compress.
- **Explain in chat, not in the paper.** Requests to "describe why" are usually about the author's
  understanding; only put the explanation in the text if asked.
- Chat renders **plain text**, not LaTeX — write `E(zY−1)^{2j}`, not `$\E(zY-1)^{2j}$`.
- **Push back when a suggestion is wrong**, with the reason. Examples that were accepted: the
  `‖A‖ ≤ ‖T_U‖` route cannot give `1/2`; `\Cref` printed "Theorem" because `lemma` shares the
  `theorem` counter; the Laplace step is used in the *inverse* direction.
- Leave `% TODO:` comments for deferred cleanups rather than silently skipping them.
- After a batch of edits, list **what to check, with line numbers**.
- Recompile after every edit and report errors/undefined references honestly.
