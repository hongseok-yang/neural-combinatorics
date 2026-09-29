# Directions for an independent case study

## Survey scope and evidentiary limits

I surveyed the available narrative histories, verbatim prompt appendices, machine-readable session indexes and final reports, ChatGPT export extracts, extraction code, catalogue, failed-route ledger, proof notes, certificate documentation and data inventories, Lean source architecture, per-row verification records, verifier documentation, file timestamps, and campaign git history. I did not inspect `history/paper/`, run Lean, rerun certificate searches, or perform a full certificate check; numerical counts below are recomputed by `history/paper_independent/survey_counts.py`.

Three named sources are not present at the supplied locations in this checkout: `lean/verification_runs/full-20260923-164651/`, `HANDOFF_ATLAS_188_171_174_153.md`, and `lean/docs/TODO.md`. The workstation raw-log backup is also absent; the second-device backup is present and its README and manifest agree with the extracted addendum, but I did not re-extract it because no doubtful turn-level extraction required that step. After fetching the current and sole GitHub branch (`main`, `535e1659`) and searching all reachable objects and commits, neither the handoff nor `lean/docs/TODO.md` occurs in Git history, so GitHub cannot restore them. The author reports personally checking the successful full verification on another device; this survey therefore treats the all-row run as author-attested, while distinguishing it from primary records inspected here and leaving its exact start/end times unspecified. Independently, the checkout statically contains 117 example files, 117 `.verified` metadata entries, and no `sorry` in those files, and the available records cover 20 bounded row runs plus the separate Atlas 43 run.

The count script deliberately does not turn token counters into money. It treats provider counters separately, counts replayed/cache-heavy fork traffic as the indexes report it, and distinguishes proof-discovery time from measured Lean build time.

The campaign boundary for the proposed papers excludes the June--July ChatGPT prehistory and the earlier odd-cycle-paper sessions. The odd-cycle result used in this project has a different proof; the earlier work may be cited as independent background but is not included in campaign totals.

The user's choices of methods, proof standards, division of labor, and resource limits are treated below as campaign design and provenance, not as findings in themselves. They enter a finding only when the record supports a further contrast or consequence.

## Departures from derived interpretations

1. I no longer recommend using A.5 as a featured example of beneficial human correction. The author recalls that the objection was mistaken and that Codex followed the resulting decision; the surviving turn instead records Codex conceding an application/documentation gap, and the general lifting theorem was not formalized. Without a fresh mathematical audit, neither retrospective interpretation is secure. A mathematics-first paper need not use this episode; any later methodology paper that makes claims about human correction should either audit it and report the result candidly or omit that claim altogether.

2. I agree with the cautious core of `history/addendum_desktop-q0hdpqd/ADDENDUM_HISTORY.md` §6—that effort tier, model, session form, instructions, and elapsed time are confounded—but not with all of its mechanics. Recomputing non-replayed turns from `addendum_index.json` gives **11** live `ultra` turns totaling **4.16 h**, not 10 turns; these belonged to seven threads/attempts (the parent plus six forks), and none closed a row.

3. The Atlas 127 provenance note and the attribution of `notes/smoothed_goodman_deflagged.tex` remain **inferred**, not logged. The style/content match, commit history, and author recollection are useful evidence, but neither surviving log store contains the producing conversation.

## Candidate findings, ranked by interest times evidentiary strength

### 1. Assurance came in distinct layers, and each layer caught a different class of error

**Finding.** Formalization did not merely confirm the incoming Atlas 43 argument: in the first 43-minute implementation turn after the broad request in A.38, Codex tested the rooted identity on the constant graphon, discovered that a repeated labelled edge had been treated unsoundly as `W^2=W`, and repaired the semantics in the same turn by introducing shared conditional Bernoulli variables. This was neither a silent patch nor a wholly new certificate: Codex prominently reported the defect and repair, amended the note and Lean layer, retained the Gram matrices and 91 coefficient identities, and kept Atlas 43 at `believed` pending completion of the remaining exact chain rather than asking the human to supply a revised proof.

**Evidence and assessment.** Logged and **strong**: workstation session `01a03722`, turn 1; commit `265afe52`; Claude Code session `d19b441c` and A.75; `notes/atlas43_exact_rooted_sos.tex`; `lean/verification_runs/atlas43/README.md`; and `lean/tools/README.md`. The observable record suggests that Codex treated the problem as a locally repairable semantic bridge because the algebraic certificate survived, but Codex's private reasoning is encrypted; this is one framework-level soundness defect affecting the rooted-SOS family, not the same mistake recurring independently in many rows. Other mistakes did recur in different forms—a reversed-Jensen draft, 65 rejected intermediate routes, and later status/audit discrepancies—but the later Claude Code audit verified the corrected Atlas 43 chain and found separate metadata/build issues rather than rediscovering `W^2=W`; the missing full-run record still limits independent confirmation.

### 2. Resource limits turned certificate design into a second proof-search problem

**Finding.** Resource failure led to three materially different responses, not an automatic search for a smaller certificate: Atlas 43 kept the large certificate but decomposed its exact reduction into 1,097 sequential modules after a monolithic attempt reached about 51 GB resident/82 GB committed; most remaining four-root rows replaced an approximately 100,000-target route with new sparse exact witnesses in better coordinates; and Atlas 127 abandoned the stronger ground-8 smoothed-Goodman route in favor of a weaker ground-6 certificate for exactly the catalogue claim, split at `2/3` to avoid a singular one-interval formulation. Formalizability therefore became a second optimization objective involving statement strength, coordinates, denominator size, sparsity, positivity witnesses, interval boundaries, and module granularity—not merely “find a smaller certificate.”

**Evidence and assessment.** Logged/source-level and **strong**: A.43--A.53, A.64--A.65, A.73--A.86, G.9--G.10, sessions `01a03722`, `01a0c2be`, and `272ea172`, the compact-certificate notes, and the per-row `completed_row.json` files. Direction was chosen by an alternating human--Codex/Claude Code control loop: the human imposed time, memory, file-count, exactness, and theorem-scope constraints and made stop/go decisions, while Codex and Claude Code diagnosed bottlenecks and proposed decomposition, factored positivity, coordinate changes, target-specific simplifications, or theorem weakening. For example, the human first sought a compact Atlas 43 route but authorized the sequential build after Claude Fable's audit, whereas for Atlas 127 Claude Opus demonstrated ground-8 infeasibility and proposed the weaker split certificate before the human authorized rationalization and formalization.

### 3. Formalization also changed the mathematics when raw certificate size was not the issue

**Finding.** Even apart from memory limits, translation into Lean repeatedly exposed simpler dependency structures: the sign of the target coefficient removed self-amalgamation/Fisher machinery for 153/171/174/188; Atlas 160 reduced 144 Bernstein coefficients to 42 plus a factorization; Atlas 178 replaced more than 900 Bernstein boxes and enumeration by three polynomial identities; several cubic/discriminant arguments became ring identities; a general forest-Sidorenko note became only the elementary instances needed by the rows; and an asymptotic even-girth theorem became 19 explicit tensor witnesses. These are not one kind of improvement: some clarify the underlying mathematics, some deliberately narrow a broad informal theorem to a row-specific claim, and some only make the proof object tractable for the prover.

**Evidence and assessment.** Logged/source-level and **strong**: the “What the Lean formalization actually proves” sections of `notes/s4_exact_interval_sos_remaining_cases.tex`, `notes/atlas160_k4_paw_edge_supporting_plane.tex`, `notes/atlas178_half_degree_weighted_k4.tex`, and related notes, corroborated by Claude Opus session `272ea172`. Together with Finding 2, this supports a process claim rather than a universal algorithm: the human supplied trust and resource policy, while Codex and Claude Code selected local mathematical refactorings whose adequacy could be checked against the exact row statement.

### 4. Codex showed methodological breadth, but its search followed a recognizable hierarchy

**Finding.** In the logged Codex proof search, the default was not to generate a generic computational certificate for every row. Codex first looked for reusable structural families and closure principles; for residual rows it repeatedly tried graph decompositions, density-sensitive transfers to known positive graphs, rooted-moment inequalities, Cauchy--Schwarz/Hölder/Jensen arguments, supporting planes, and exact low-dimensional polynomial certificates; when a proposed bridge failed, Codex often constructed an exact rational counterexample to that intermediate lemma and tried a different reduction. General rooted-SOS certificates appeared later as the bulk method for the analytically resistant residue, so the record shows adaptive methodological breadth together with a clear bias toward compositional, human-readable arguments before general certificate search.

**Evidence and assessment.** Logged/source-level and **strong for the observed ordering and breadth, but only suggestive of an intrinsic Codex preference**. The Codex-authored handoff in A.35/A.36 explicitly says “Start with a structural family rather than 28 unrelated calculations” and prioritizes density-sensitive comparison, mixed-chordal compatibility, rooted moments, supporting planes, and decomposition; Codex sessions `019ff9a1` and `01a012c6` then enact that plan, while Attempts 33--65 document repeated transfer, gluing, moment, tangent-plane, and correlation failures before the later Codex rooted-SOS campaign closed most remaining rows. The hierarchy was partly elicited: the human prioritized positive results, requested “more principled methodologies,” and for one long stretch restricted Codex to Turán-local and high-density tests. The defensible claim is therefore that Codex could select and execute many mathematically distinct approaches and change route after exact failure—not that an unprompted model has a stable universal proof-search preference.

### 5. The breakthrough occurred in a suitable effort regime for building reusable proof infrastructure

**Finding.** The evidence is better described as a suitable operating regime than as either “more reasoning effort is always better” or “higher effort is unhelpful.” The successful 10.5-hour `xhigh` turn combined substantial deliberation with a fresh continuous autonomous session, an explicit certificate-oriented method contract, and enough runtime to change the unit of work from a row-level proof attempt to reusable proof infrastructure. It first spent roughly 90 minutes auditing structural and analytic routes; after escalating to direct rooted SOS, it developed in one continuous turn a three-root house certificate, a general four-root interval-SOS framework, exact `S_3`/`S_4` symmetry reduction, equality-driven facial reduction, rational reconstruction, exact positivity by diagonal dominance, and an independent coefficient checker. Once the first general four-root certificate was exact, the same discovery-to-verification loop was reused across rows, ultimately closing 18 of the remaining 20.

**Evidence and assessment.** The visible progress record of `01a0349f` turn 0 is unusually detailed and **strong on mechanism**: at 03:08 it enlarged the house search to three shared labels, at 04:04 it had an exact 91-identity Atlas 43 certificate, at 04:32 it introduced the complete symmetry-reduced four-root cone, at 05:23 the first 407-identity four-root certificate was exact, and by 07:46 eleven cases were closed; the final report at 12:03 records 18 of 20. The turn created about 26 experimental programs plus the two proof notes and repeatedly distinguished solver failure, infeasible ansatz, boundary face, and exact proof rather than counting numerical feasibility. These were not untouched rows: a conservative literal audit of the 65-entry failure ledger finds at least 23 distinct entries explicitly mentioning one of the 18 rows closed in this turn, or 31 entries when the two partially solved rows 130 and 203 are included. The distribution is highly uneven—Atlas 43, 130, and 157 alone appear in 7, 10, and 8 ledger sections, whereas 118/122/124, 151, 185, and 194 have no row-named entry—so the strongest claim is that the reusable certificate machinery simultaneously broke several long-standing bottlenecks and made lightly explored rows cheap to close.

The logs do **not** identify `xhigh` itself as a causal sweet spot. On the second device there was no long `high` proving execution: `high` turns were bookkeeping or post-result Q&A, while the preceding unsuccessful work ran at `xhigh` and `ultra`; the only logged `high` proving attempt elsewhere was a 28-minute audit that closed no row. The seven `ultra` attempts had 4.16 combined hours but at most 73 minutes per turn, inherited a mature interactive thread, and pursued local partials and implications, whereas D.87 launched a fresh autonomous `/goal`, explicitly authorized exact SoS/Bernstein certificates, and allowed a continuous 10.5-hour architecture-building run. The defensible conclusion is therefore that reasoning effort must be matched to search horizon, continuity, and task design: this campaign found one highly productive configuration, but it did not run the controls needed to separate the effort setting from those other ingredients. Private reasoning is encrypted, so “ambition” remains an interpretation of observable tool-building behavior.

### 6. Prompts and handoff documents became part of the technical infrastructure

**Finding.** Three long Codex objectives were drafted by Codex itself and pasted back by the human, while Claude Fable wrote the later handoff for Claude Opus; these objects carried counts, accepted methods, forbidden shortcuts, resource constraints, and failure policy across sessions. **Evidence and assessment.** Logged and **strong for provenance, suggestive for effectiveness**: A.9, A.17--A.18/G.2, A.35--A.36/G.5, A.81, prompt provenance notes, Codex sessions `019ff8c8`, `019ff931`, and `019ff9a1`, and Claude Fable session `d19b441c`; the missing handoff file prevents a fresh content audit, and no counterfactual shows that a shorter prompt would have failed.

### 7. Broad theorem production and row closure were different notions of progress

**Finding.** The ChatGPT chordal-entropy extension gave a broad sufficient condition beyond pure chordality and the four-day house thread improved partial intervals, yet the hard open rows remained until exact row certificates were constructed. **Evidence and assessment.** Logged and **strong as an outcome comparison**: `notes/chordal_entropy_extension.tex`, conversations `6a856564`, `6a8ab440`, `6a871354`, and `6a8961a4`, followed by `01a0349f`; it would be unfair to call the theorem “unproductive”—its breadth is mathematically valuable—so the surprise is that conceptual generality and completion of a finite classification ranked progress differently.

### 8. Parallel Codex forks and Claude subagents helped reconnaissance more clearly than closure

**Finding.** The six `ultra` forks shared a working tree and produced partial ranges, conditional arrows, audits, and reusable files but no completed row; later three Claude Opus subagents mapped separate verification routes before a main Opus session executed them. **Evidence and assessment.** Logged and **suggestive**: D.83--D.86, the `01a02f*` final reports, `d19b441c` subagent records, and `272ea172`; the first experiment had shared-state interference and short runs, while the second concerned planning rather than independent proof search, so the material cannot rank parallel against serial strategies generally.

### 9. The shared catalogue was effective memory and also a source of epistemic drift

**Finding.** A generated 117-row table kept status, witnesses, proof reasons, and Lean state visible across Codex and Claude Code sessions, but prose sections and architecture documents lagged, `Counts.lean` was corrected only after completion, and Atlas 43/196 source metadata said `.verified` for roughly four weeks before the measured chain build. **Evidence and assessment.** Logged/source-level and **strong**: A.4, `GRAPH_CLASSIFICATION_UP_TO_6_VERTICES.md`, `LEAN_VERIFICATION_ARCHITECTURE.md`, commits `265afe52`, `4231a841`, `690d0218`, and `e2d96440`; the current table is internally consistent, so the lesson is about generated state plus independent validation rather than the unreliability of catalogues as such.

### 10. A failed-route ledger made negative knowledge a first-class output

**Finding.** `FAILED_PROOF_ATTEMPTS.md` contains 65 numbered routes, often with exact rational counterexamples to an intermediate lemma even when the target row is positive, which separates “this proof idea fails” from “the theorem fails.” **Evidence and assessment.** Logged/source-level and **strong for existence, suggestive for benefit**: G.4, sessions `019ff9a1` and `01a012c6`, and the ledger (for example Attempt 32 and Attempts 33--65); there is no measure of avoided duplicate work and the ledger itself consumed context, but it is unusually inspectable scientific residue from an AI search.

### 11. Calibration was often good locally but failed at the metadata boundary

**Finding.** Codex rejected its reversed-Jensen Atlas 178 draft, reported its Atlas 203 solver failure as “no certificate or mathematical conclusion,” and repeatedly labelled ChatGPT Pro outputs partial, yet Codex-authored Atlas 43/196 source metadata asserted verification before Claude Fable's later sequential audit. **Evidence and assessment.** Logged and **strong**: Codex session `01a012c6` turn 0, Codex session `01a0349f` turn 0 and its final report, E.9--E.16/E.23--E.25, commit `265afe52`, and A.75; these examples oppose any single “honest” or “overconfident” label and suggest that interface/state transitions deserve more scrutiny than final prose alone.

### 12. The observed cost was large, heterogeneous, and incompletely monetizable

**Finding.** The workstation Codex indexes report 1.912 billion processed tokens (1.868 billion cached input), the second-device primary Codex threads report 669 million more, and surviving Claude Code sessions report 283.5 million input tokens including cache; in the clearest wall-clock comparison, a 10.5-hour Codex discovery turn closed 18 rows, a later 17.5-hour Codex verification goal run completed 15 rows, the 20 bounded row builds total 11.69 hours, and Atlas 43 adds 6.0 hours. The author reports paying KRW 159,000 per month for ChatGPT Pro and Claude Max charges of USD 96.76 on 21 July and USD 110 on 21 September. **Evidence and assessment.** Logged and **strong for the counters, weak for a complete proof/verification split or financial cost**: Codex sessions `01a0349f` and `01a0c2be`, the indexes, per-row records, and `survey_counts.py`; the subscriptions covered activity beyond this campaign, the sessions mix proving, programming, and audit work, the build total is nested within Codex/Claude Code session time, and missing August Claude Code usage, energy, and human attention prevent either an additive time total or a defensible campaign-specific cost.

### 13. Reproducibility is stronger for final theorem artifacts than for discovery

**Finding.** The repository retains exact witnesses, rational checkers, generated Lean sources, 20 per-row build manifests, and the Atlas 43 chain record, while numerical SDP workspaces, deleted transcripts, encrypted reasoning, environment-sensitive Young bases, and the absent full-run directory prevent exact replay of how the proofs were found. **Evidence and assessment.** Source-level/logged and **strong**: certificate notes and checkers, `lean/verification_runs/atlasNNN/`, `lean/verification_runs/atlas43/README.md`, extraction-script caveats, and Claude Opus session `272ea172`; the author-attested all-row build and the current 117 source files with no `sorry` support the final result, while the missing source-12 report prevents an independent audit of that build's timing and environment from this checkout.

### 14. The formal development usually proves the classification row, not every general theorem in the notes

**Finding.** General forest Sidorenko, universal lifting, asymptotic even-girth constructions, and the stronger smoothed-Goodman statement were often replaced in Lean by elementary instances, explicit exact witnesses, or weaker row-specific certificates sufficient for the 117 propositions. **Evidence and assessment.** Source-level and **strong**: `notes/forest_cone.tex`, `notes/clique_oddcycle_join.tex`, `notes/even_girth_false.tex`, `notes/smoothed_goodman_deflagged.tex`, the compact-certificate notes, and their Lean-correspondence sections; this narrows claims about formalized mathematics but also yields a clear distinction between theorem discovery and classification verification.

### 15. Reconstructing the campaign is itself a forensic result

**Finding.** The chronology had to be assembled from rollout indexes, final reports, git trailers, file timestamps, a web export with missing reasoning/files, and retention-deleted Claude work, and the reconstruction still leaves explicit uncertainty. **Evidence and assessment.** Logged/inferred and **strong**: `history/tools/`, addendum extraction code, `lean_file_timestamps_2026-09-23.json`, git, and source-gap discussions in both histories; this is interesting to AI-science readers because an apparently comprehensive activity log still does not automatically yield reliable provenance.

### 16. Human non-authorship of the proof artifacts is an explicit author statement, corroborated where logs survive

**Finding.** The author states that neither the author nor the co-author wrote proof text, certificates, scripts, or Lean code for this campaign; both only prompted Codex, Claude Code, or ChatGPT Pro and transferred the resulting artifacts. Surviving sessions corroborate this wherever patch-level records exist. **Evidence and assessment.** This is an explicit authorship declaration supported, but not universally provable, by the A/D/E prompt corpora, file-patch records, commit trailers, and timestamp reconstruction; deleted Claude Code transcripts and pasted external outputs mean the paper should identify it as an author statement rather than claim that the archive proves a universal negative.

### 17. The automatic approval reviewer left almost no observable scientific trace

**Finding.** Across both devices it allowed all 45 recorded requests, mostly installs, git operations, or cleanup, while Claude's separate permission mode did redirect permanent deletion into a trash move. **Evidence and assessment.** Logged and **anecdotal**: 29 workstation and 16 second-device reviewer turns in the indexes, plus A.69--A.71; absence of a denial does not show the reviewer was useless—it may have deterred risky requests—but this is a useful negative finding about what the campaign logs can and cannot attribute to automated oversight.

## Article directions

Every direction below retains a precise main-text classification theorem and the complete mathematical, certificate, counterexample, formal-verification, and provenance appendices required by the brief. The difference is the claim made by the main text.

### Direction A — layered assurance (recommended spine)

**Working title:** *Proof, Certificate, Kernel, Audit: Anatomy of a 117-Row AI-Assisted Classification*

**Thesis.** The most informative unit in this campaign is not a Codex, Claude Code, or ChatGPT Pro answer but a claim moving through non-equivalent states: heuristic route, human-readable proof, exact finite certificate, Lean theorem, metadata/axiom audit, and fresh source build. The case study shows both the value and the gaps of this stack: one layer repairs shared-edge semantics, another catches a verification-status error, and resource-bounded formalization feeds back into the proof itself.

**Readers.** AI-for-mathematics, formal methods, computer-assisted proof, and mathematicians evaluating whether a Codex- and Claude Code-produced classification is trustworthy.

**Main-text findings.** Findings 1, 2, 3, 9, and 13; a shorter orchestration section uses 5--6 as context. Detailed row proofs, certificate identities, all 23 witnesses, the full status table, and note/Lean deviation inventory move to mathematical appendices.

**Figures and tables.** (i) A pipeline diagram with the `W^2=W` repair and Atlas 43 status lag placed at the layer that caught each; (ii) a timeline with mathematical status and formal status as separate curves; (iii) an evidence matrix for all 117 rows (informal proof / exact checker / Lean / fresh build); (iv) time-memory scatterplots for the 20 bounded rows plus Atlas 43; (v) a table of formalization-induced proof changes.

**Evidence profile and risks.** The error chronology, note/Lean differences, and per-row resource data are strong. The author personally checked the all-row build on another device, but its missing source-12 report prevents this survey from reconstructing the exact run. The main risks are making a single campaign sound like a universal assurance recipe, letting process eclipse the graphon theorem, and excessive length.

**Estimated length.** 30--35 pages of main text plus 80--120 pages of mathematical/formal appendices.

### Direction B — resource-bounded mathematics

**Working title:** *Proofs Under 16 GiB: How Machine Limits Reshaped an AI-Generated Classification*

**Thesis.** Treat the one-hour, 16-GiB, roughly 100-file envelope as the main experimental intervention. The campaign's most concrete feedback loop runs from memory blow-up to representation changes, interval splits, smaller exact certificates, weaker sufficient theorems, and finally kernel-checkable rows; constraints did not merely accelerate verification but selected which mathematics entered the formal result.

**Readers.** Formal proof engineers, computational mathematicians, proof-certificate designers, and AI researchers interested in long-horizon artifact optimization.

**Main-text findings.** Findings 2, 3, 12, 13, and 14. The Codex/Claude Code chronology, prompt corpus, and detailed division of labor are compressed into a provenance section; complete mathematics stays in the required appendices.

**Figures and tables.** (i) Before/after proof-object sizes from the 51-GB Atlas 43 approach to compact rows; (ii) build time, peak memory, file count, and source bytes per row; (iii) Atlas 127's ground-8-to-ground-6/single-interval-to-split-interval transformation; (iv) a Sankey-style map from informal methods to formal replacements; (v) the resource envelope with pass/fail/repair events.

**Evidence profile and risks.** September build records and the Atlas 43 logs are unusually strong, while precise discovery compute and energy cost are missing. The framing may look like systems engineering rather than AI-assisted mathematics, and “constraints improved mathematics” must be reserved for cases such as the unnecessary 153 argument rather than every compression.

**Estimated length.** 25--30 pages of main text plus 85--125 pages of appendices.

### Direction C — orchestration by one mathematician

**Working title:** *One Mathematician, Codex, Claude Code, and ChatGPT Pro: Orchestrating a Formalized Graphon Classification*

**Thesis.** The central object is a human-directed organization: Codex, Claude Code, and ChatGPT Pro work interactively, autonomously, in forks, and through web conversations; the catalogue, failure ledger, exactness rules, and Codex- or Claude-authored handoffs substitute for shared memory. The article asks which forms of direction changed the work and why higher Codex reasoning effort or more parallel Codex attempts did not by themselves predict closure.

**Readers.** AI-systems, HCI, AI-for-science, and lab-automation researchers, with mathematicians as a secondary process audience.

**Main-text findings.** Findings 5--8 and 16, with Findings 1--3 summarized as the technical outcome. Certificate details, per-row proofs, and most build engineering move to appendices.

**Figures and tables.** (i) A vendor/interface swimlane timeline; (ii) a handoff graph linking prompts, notes, commits, and Lean modules; (iii) catalogue-state transitions annotated by human prompts; (iv) productive/unproductive run comparison with all confounders shown; (v) a division-of-labor table using logged versus inferred attribution.

**Evidence profile and risks.** Surviving prompt and turn records are rich, but deleted August Claude logs and inferred Atlas 127/co-author provenance cut directly across the thesis. The largest risks are causal overclaiming without controls, treating token volume as effort, privacy/credit errors, and sounding like a model comparison when multiple variables changed together.

**Estimated length.** 35--40 pages of main text plus 80--120 pages of appendices.

### Direction D — forensic reconstruction and scientific provenance

**Working title:** *Can an AI-Assisted Proof Campaign Be Reconstructed? Evidence from a 117-Case Classification*

**Thesis.** Use the completed theorem as a test case for whether modern Codex, Claude Code, and ChatGPT Pro logs, git, timestamps, generated catalogues, and proof artifacts suffice to reconstruct scientific provenance. The answer is mixed: final mathematical objects are inspectable, but reasoning is encrypted, exports omit files, retention deletes sessions, generated prose drifts, and several attributions remain probabilistic.

**Readers.** Reproducibility, research-integrity, provenance, and AI-for-science communities, alongside formal-methods readers.

**Main-text findings.** Findings 9, 11, 13, 15, and 16. The campaign narrative becomes an evidence audit rather than a heroic chronology; the mathematics remains fully available in appendices.

**Figures and tables.** (i) A source-provenance graph marking logged, derived, inferred, missing, and contradicted edges; (ii) a reconstruction timeline showing when evidence was produced versus recovered; (iii) an attribution-confidence table; (iv) a “claim versus supporting layer” matrix; (v) a missing-data table with consequences.

**Evidence profile and risks.** The extraction code and surviving artifacts make the provenance analysis strong, and the explicit gaps prevent false completeness. The risks are that the graphon result feels like an example rather than a contribution, missing-source discussion dominates, and quoting candid operational failures creates privacy and tone concerns.

**Estimated length.** 28--35 pages of main text plus 80--120 pages of appendices.

### Direction E — mathematics first, AI as provenance

**Working title:** *The Chromatic-Polynomial Graphon Bound for Graphs on at Most Six Vertices*

**Thesis.** Present the 94/23 classification as the principal contribution: analytic families explain most positive rows, exact rooted/four-root certificates close a concentrated residue, and three exact counterexample mechanisms cover all negative rows. For Atlas 127, the direct ground-6 split certificate is the principal proof; the stronger smoothed-Goodman theorem is contextual mathematics, not the formal route. The Codex/Claude Code/ChatGPT Pro campaign appears in a focused methods/provenance section explaining how the theorem and formalization were produced, checked, and changed.

**Readers.** Extremal combinatorics and graphon researchers first; computer-assisted proof and AI-for-mathematics readers second.

**Main-text findings.** Findings 3, 4, 7, 13, and 14. Most process chronology, token accounting, prompt analysis, and model comparisons move to a case-study appendix, while mathematical ideas and representative certificates move into the main text.

**Figures and tables.** (i) The 117-graph atlas colored by method and sign; (ii) a method-family coverage table; (iii) density-interval coverage diagrams for certificate rows; (iv) exact-witness family diagrams; (v) a note-versus-Lean theorem map.

**Evidence profile and risks.** The table, notes, exact data, Lean source, and author-attested all-row build give this direction a strong base, subject to a full audit of outside theorems; the missing source-12 report limits only independent reconstruction of the final run's timing and environment. It best serves mathematicians but deliberately leaves most process evidence to a companion study.

**Estimated length.** 20--25 pages of main text plus 100--140 pages of mathematical/formal appendices.

## Recommendation

I recommend two companion papers. The first should follow Direction E and stand independently as a mathematics paper: the 94/23 theorem, proof families, exact certificates, counterexamples, and Lean verification are the principal contributions. Direction A's assurance layers and Direction B's resource-bounded transformations belong in focused technical sections rather than serving as headline claims. Direction D belongs in limitations.

The second paper should be a redesigned Direction C. The present campaign can motivate hypotheses about long-horizon Codex work, Claude Code formalization, structured handoffs, and resource-aware proof design, but the historical record is observational and confounded. A strong methods paper would test a prespecified workflow in clean workspaces, ideally with repeated matched-budget runs and Lean-verified rows—not claimed proofs—as the primary endpoint.

## Editorial policy for conversation evidence

The main text should use professional, neutral prose. For example: “A parallel Lean build exhausted memory” or “Codex reported that Atlas 43 was not yet verified end-to-end.” It should not reproduce informal wording merely for dramatic effect.

A chronological supplementary appendix should preserve the substantial exchanges needed to audit these statements. Each excerpt should include a stable label, date and time, speaker, system and model where applicable, session identifier, prompt identifier, and the relevant prompt-response context. Suitable units are labels such as **Excerpt B.2.3**, grouped under timeline subsections such as **B.2 Resource failure and sequential verification**. The main text should cite the stable unit—“A parallel Lean build exhausted memory (Supplementary Appendix B, §B.2, Excerpt B.2.3)”—rather than a mutable source-file line number. Page or line references can be added by the final typesetting system.

The appendix should reproduce selected text verbatim, retain original wording and typographical errors, mark omitted material explicitly, and link each excerpt to the corresponding full prompt appendix or machine-readable session record. Selection should follow a declared rule: include exchanges that materially changed mathematical correctness, proof status, verification scope, resource policy, or research direction. This permits transparent inspection without importing conversational tone into the mathematical exposition. A.5 remains outside the recommended narrative unless it is mathematically re-audited and becomes necessary for a methodology claim.
