# Experiments

The results of every experiment of the prover, from the unguided engine to LLM agents and
learned models, in one place. Each section gives the question, the setup in brief, the
numbers and what they mean; the details are in `DESIGN.md`, in the section named at the
head of each.

**Conditions common to all searches:**
- the corpus is the set.mm translation (47,611 proofs) and the MM0 files of
  `scripts/build-corpus.sh`: the compiler's `hello_mmc`, `mm0`, `peano`, `hol`, `set`;
- 12 searches at once on a machine of 24 threads (one per physical core);
- time limits are wall clock, so two runs of the same code differ: on set.mm's test part,
  `learned` at 1 s gave 82, 83, 83, 84 and 84 in five runs. Differences of 2 or 3 are
  noise;
- every proof found is checked by the verifier. No run in this file had a proof
  rejected.

## Summary

| experiment | date | outcome |
|---|---|---|
| Replay of every set.mm proof from its skeleton | 2026-10-12 | 47,611 of 47,611, accepted by `mm0-rs` |
| Unguided breadth-first search, 1 s | 2026-10-12 | 55% of propositional, 33% of predicate calculus |
| Proof rails (replayed subproofs of earlier proofs) | 2026-10-17 | **+54%** on set.mm at 1 s |
| `guided`: closing rails and one open rail by recency | 2026-10-17 | 110 against 66 for `bfs` on every 40th theorem |
| LLM agents through MCP (pilots) | 2026-10-16 | 7 of 7 proved, mostly from the model's memory |
| Agent bench, Whitehead against MM1 | 2026-10-17/18 | **the hypothesis fails:** MM1 agent 30 of 30 at $3.69, Whitehead agent 26 of 30 at $19.87 |
| Whitehead as a gap filler for an MM1 agent | 2026-10-18 | no gain: 8 of 58 holes filled, more tokens |
| Learned ranking of variants (`learned`) | 2026-10-18 | **+52%** over `guided` on set.mm's test part at 5 s |
| Files weighed evenly | 2026-10-18 | mm0 +2.4% offline, search the same |
| Cheaper features | 2026-10-18 | 22% faster; expansion, not scoring, now limits |
| Expert iteration, one round | 2026-10-19 | no gain |
| Value of goals | 2026-10-19 | +5% at 1 s and +3% at 5 s, losing nothing; +10% at 5 s if mm0 may lose a fifth |
| The subgoal bench: what search closes of the subgoals of known proofs | 2026-10-21 | `learned` 67% in 100 ms, 72% in 500 ms; the failures are binders and the theorem's own matter; procedures can add 7.5 points at most |

## 1. The engine without guidance

### The replay test (`DESIGN.md`, "The replay test")

Each proof is given as the tree of assertions it uses, with every expression forgotten;
the engine finds every substitution by unification.

| | |
|---|---|
| reconstructed | 47,611 of 47,611 |
| steps | 3,508,182, as in the file |
| time | 77 s on one processor, 8.8 s on 24 |

`mm0-rs`, mm0-c and our verifier accept the result.

### The replay over the full expansion (`DESIGN.md`, "The replay over the full expansion")

Every goal node gets all its variants, and the known proof's are chosen; the proofs of
the others meet it in the joins. With the default limits (60 s, 2M assertion nodes):
46,254 of 47,611 found, 282 by another proof than the known one, 1,357 stopped at a limit;
1 h 57 min on 24 threads, 25 GB at most. The theorems that stop have long proofs, with
bare-variable subgoals that unify with nearly every conclusion.

### The search test (`DESIGN.md`, "The search test")

Breadth first, nothing to rank the variants, 1 s per theorem.

| | propositional calculus | predicate calculus |
|---|---|---|
| theorems | 1,520 | 1,262 |
| proved at 1 s | 840 (55%) | 422 (33%) |
| largest proof found | 4 steps | 3 steps |

- In one second the tree reaches depth 3 to 4 (about 500,000 assertion nodes).
- On every 10th theorem, 10 s instead of 1 s: 79% and 49% instead of 56% and 32%, and no
  proof longer than 4 steps.
- Backward and forward in turn: 108 and 46 of the sample (154, 127), against 89 and 41
  backward alone, and proofs of 5 steps.

## 2. How many variants there are to choose from (`DESIGN.md`, "Measurement")

At each goal node on a known proof's path, every assertion that unifies with the goal.
set.mm, every 20th theorem (84,703 nodes):

- the median node has 988 variants, the 90th percentile 8,967, the largest 48,940;
- 8.2% of nodes have more than 10,000.

What a description of the next goals leaves (a filter an agent could write), every 40th
theorem:

| | median left | 5 or fewer left |
|---|---|---|
| all variants | 983 | 0% |
| next goals described to depth 1 | 114 | 9.2% |
| to depth 2 | 32 | 25.8% |
| to depth 3 | 16 | 39.5% |

Ordering by uses in earlier proofs puts the known variant first at 7.9% of the nodes
among all, and at 57.0% among those described to depth 3. Steps without premises are a
third of the nodes, and no description narrows them.

## 3. Chains and subproofs of set.mm (`STATUS.md`, "Phase 4: the chains"; `DESIGN.md`, "Proof rails")

- **Chains** of 2 to 6 steps: 96.5% of all steps lie on a chain of 2 steps or more that
  occurs at least twice, 23.3% on one that occurs 1,000 times.
- **Distinct subproofs below a node:** 664,589 in 3.5M steps; a lemma for each takes 11 s
  to make.
- **Coverage:** 43.2% of the steps lie inside a subproof that an earlier proof already has
  (each counted once per proof).
- **Cost:** a lemma for every subproof multiplies the variants of a goal by about 6 at the
  median. Hence rails, replayed at a goal, rather than lemmas.

## 4. Rails and composable tactics (`DESIGN.md`, "Proof rails", "Ranks for the rails")

Subproofs of earlier proofs are put down at a goal and followed step by step; the open
goals they leave are searched breadth first.

**Rails that close the goal** (`rails(10, rank=reach, open=0, upto=1)`):

| sample | per theorem | breadth first | rails |
|---|---|---|---|
| set.mm, every 40th (1,198) | 1 s | 67 | **103** (+54%) |
| | 5 s | 92 | **122** (+33%) |
| the calculus, every 10th (281) | 1 s | 139 | **160** (+15%) |
| | 5 s | 173 | 173 |

**Rails that leave goals open** lost at first: by occurrences, 70 against 139 at 1 s on
the calculus. The best of the first 3 rails agreed with the known proof in half its steps
for 1.2% of the theorems. Better ranks, offline:

| rank of open rails | the known proof's first step | half its steps |
|---|---|---|
| occurrences | 8.8% | 1.2% |
| specific (most non-variable nodes in the conclusion) | 19.1% | 3.4% |
| recent (in the latest proof before) | 12.4% | 2.5% |
| a linear model | 19.9% | 3.4% |

**`guided`**, the closing rails plus one open rail by `recent` at the root:

| tactic | set.mm (1,198), 1 s | calculus (281), 1 s | set.mm, 5 s | calculus, 5 s |
|---|---|---|---|---|
| `bfs` | 66 | 134 | 91 | 170 |
| best rails before | 102 | 159 | 122 | 170 |
| **`guided`** | **110** | **173** | **127** | **188** |

The composable tactics were checked against the strategies they replaced: on set.mm, the
definitions and the old strategies gave the same output theorem for theorem (endings,
steps, nodes, joins), in five configurations.

## 5. LLM agents

### Pilots through the MCP server (`DESIGN.md`, "The session")

A Claude subagent proved set.mm theorems that breadth first does not prove in 1 s, by
choosing variants with filters, intermediate goals and runs.

| pilot | theorems | proved | calls |
|---|---|---|---|
| names shown | `jaob`, `pm5_32`, `baroco` | 3 of 3 | 15, 25, 10 |
| names hidden (`--anonymous`) | `jaob`, `pm5_17`, `biadanid`, `_3ianor` | 4 of 4 | 13, 24, 25, 23 |

- With names, the agent chose nearly every step from its memory of set.mm.
- Without names it recognized familiar rules by their statements. Shape filters on the
  next goals took hundreds of variants to 1–4.

### The agent bench: Whitehead against MM1 (`DESIGN.md`, "The agent bench")

**The hypothesis (the author's):** an agent that proves through Whitehead spends less
time and fewer tokens than one that writes MM1 and checks it with `mm0-rs`, at a price in
memory.

**Setup:**
- two `claude -p` agents, Sonnet 5.5, high effort, the same limits, each in its own
  directory with nothing else loaded;
- the Whitehead agent has the MCP server on peano; the MM1 agent has `./check`;
- both have the library up to the theorem and `./search`;
- ten theorems of `peano.mm1`, 3 to 48 steps;
- the cost is the tokens at list prices.

**Round 1, the library as it is:** both proved all ten. MM1: 1.04M tokens, $0.81.
Whitehead: 14.2M tokens, $4.74. But the MM1 agent wrote the library's own proof, character
for character, on four theorems: it remembered `peano.mm1`.

**Round 2, every theorem renamed, three runs of each pair** (tokens in thousands):

| theorem | Whitehead | MM1 | median W/M |
|---|---|---|---|
| `mt2` | +75 +75 +75 | +72 +50 +53 | 1.4 |
| `bibi1` | +75 +75 +75 | +134 +149 +177 | 0.5 |
| `eor` | +327 +336 +360 | +137 +192 +89 | 2.5 |
| `sucsub` | +521 +832 +310 | +97 +148 +124 | 4.2 |
| `notfal` | +527 +254 +232 | +99 +84 +98 | 2.6 |
| `mulmoddir` | +1289 +695 +1359 | +87 +93 +90 | 14.3 |
| `ssasym` | +880 +1777 +1886 | +134 +192 +122 | 13.2 |
| `addcom` | +4827 +4743 −6530 | +121 +164 +179 | 29.4 |
| `dvdasymd` | +2731 +6136 +4231 | +334 +188 +233 | 18.2 |
| `divmod` | −6931 −6836 −6026 | +319 +556 +446 | 15.3 |

(+ proved, − not proved.)

| | Whitehead agent | MM1 agent |
|---|---|---|
| proved | 26 of 30 | 30 of 30 |
| cost at list prices | $19.87 | $3.69 |
| memory, at most | 2.1 GB (the server) | 15 MB (`mm0-rs`) |
| calls per task | 14 to 174 | 5 to 16 |

**Harder theorems** (60 to 115 steps, one run each):

| theorem | steps | Whitehead | MM1 | tokens W/M |
|---|---|---|---|---|
| `leasymd` | 60 | proved, 11.8M, $3.13 | proved, 0.58M, $0.41 | 20.4 |
| `ltmul1` | 64 | proved, 2.5M, $0.86 | proved, 0.44M, $0.26 | 5.7 |
| `dvdadd1` | 67 | proved, 5.5M, $1.61 | proved, 0.38M, $0.25 | 14.7 |
| `prth` | 69 | proved, 8.2M, $2.33 | proved, 0.55M, $0.35 | 14.9 |
| `divlem3` | 111 | not proved, 12.8M, $3.84 | proved, 0.96M, $0.73 | 13.4 |
| `appendnth1` | 115 | not proved, 7.5M, $2.81 | proved, 1.90M, $1.03 | 4.0 |

**What it means:**
- **The hypothesis does not hold,** for this model and this interface. Whitehead is
  cheaper only where `guided` proves the theorem at once.
- **The tokens follow the calls.** Each call reads the whole context again. The MM1 agent
  writes a whole proof term and lets MM1's elaborator decide the metavariables by
  unification, in a few calls. The Whitehead agent goes through the tree a step at a time.
- **MM1's elaborator already does for the agent what the engine was to do.** What
  Whitehead adds is search, and an agent that can name the lemmas needs little of it.
- **Caveats:** one model; the model knows MM1 from its training and meets Whitehead's
  tools for the first time; three runs per pair; set.mm has no MM1 source to try.

### Whitehead as a gap filler (`DESIGN.md`, "Whitehead as a gap filler")

The MM1 agent writes the structure of a proof with holes; `./fill` closes each hole whose
goal has no metavariable by a Whitehead search (`prove goal`, printed as an MM1 term).

| | proved | tokens | cost |
|---|---|---|---|
| ladder, hybrid agent | 10 of 10 | 2.67M | $1.68 |
| ladder, MM1 agent (median of 3) | 10 of 10 | 1.63M | $1.24 |
| harder theorems, hybrid | 6 of 6 | 9.30M | $4.57 |
| harder theorems, MM1 | 6 of 6 | 4.80M | $3.03 |

- Of 58 holes tried, 8 were filled (proofs of 1 to 41 steps).
- 38 holes found no proof in 5 to 40 s. They were arithmetic identities
  (`b * suc q + 0 = b * q + b`) and facts of order and divisibility.
- 14 holes named variables of the agent's own (an induction it started).
- **What it means:** the holes an agent leaves are the steps it finds hard, and those are
  beyond a breadth-first search. They ask for decision procedures (arithmetic
  normalization, linear arithmetic, tautologies): the oracles of layer 2.

## 6. The learned ranking layer (`DESIGN.md`, "The learned ranking layer")

A small model, called at every goal, instead of an LLM called rarely: Whitehead's tree as
the environment of a learned policy.

**Setup:**
- **Data** (`prove export`): at each goal node on a known proof's path, every variant, the
  known one labelled 1. 23 features: uses, recency, the new goals, the shared symbols.
- **Corpus:** every MM0 file, each theorem once. Each file is split in its order: the
  first 80% to train, 10% to tune, 10% to test.
- **Models:** trained in Python (LightGBM) and evaluated in Lean (`--model`). Lean's scores
  equal Python's to 5·10⁻⁷.
- **Search:** `learned`, which is `guided` with each step costing its place among its
  goal's variants by the model, divided by 5. The premise-free variants are tried first at
  the root.

### The ranker, offline

Where the known variant ranks among all the variants of a node, set.mm's test theorems
(16,631 nodes, a median of 1,076 variants a node):

| model | first | in the first 10 | MRR |
|---|---|---|---|
| by uses | 6.1% | 27.0% | 0.135 |
| by recency | 9.4% | 40.6% | 0.193 |
| linear | 18.6% | 53.0% | 0.296 |
| boosted trees (846) | 22.3% | 58.4% | 0.339 |
| boosted trees, the first 100 | 20.4% | 58.1% | 0.325 |

### The ranker in search (the test parts only)

| test part | per theorem | `bfs` | `guided` | `learned` |
|---|---|---|---|---|
| set.mm (618) | 1 s | 25 | 61 | **82** |
| | 5 s | 29 | 67 | **102** (+52% over `guided`) |
| the compiler (505) | 1 s | 501 | 496 | **505** |
| mm0's own (491) | 1 s | 102 | 244 | 233 |
| | 5 s | 247 | 248 | 238 |

- **Speed decides.** With 846 trees, a search expands 2 nodes a second at the median; with
  100 it is 8 times faster and proves more (79 against 71).
- **A step without premises must not wait for its place.** On the compiler, the model put
  one-step lemmas low, and the search lost a third of what `bfs` proves (342 against
  501). Trying them first at the root fixes it (505).
- **On mm0** `learned` is 4% below `guided`: 89% of the training rows are set.mm's.

### Step 1: the files weighed evenly

Each file's nodes share a total weight of the square root of its number of nodes.

- **Offline**, among a node's known variant and 50 others: mm0 65.5% first, against
  63.1%; set.mm unchanged at 81.7%.
- **In search at 1 s:** set.mm 84 (82), the compiler 505, mm0 229 (233). The same,
  within noise.
- **What mm0 loses is one family:** the congruences `elabDefOeq1d` … `8d`, long proofs of
  one shape, which the rails find and the model's order delays.

### Step 2: cheaper features

What depends on the rule alone is computed once for the file, and what depends on the
goal once for all its variants.

- **Features:** 5.0 µs to 3.9 µs a variant. **Score of 100 trees:** 4.1 µs to 3.9 µs.
- **The ceiling:** ranking by uses costs nothing. With it a search expands 17 nodes a
  second at the median, against 15–16 with the model, and it proves 67 at 1 s, against
  83 with the model. Scoring no longer limits the search; expanding does.

### Step 3: expert iteration, one round

`learned` searched every training theorem for 1 s. Where its proof differed from the
known one, the rows along it were added to the training data.

| file | training theorems | proved | in another shape | rows added |
|---|---|---|---|---|
| set.mm | 38,087 | 5,520 | 3,737 | 927,000 |
| the compiler | 8,109 | 2,821 | 2,280 | 430,000 |
| mm0 | 3,900 | 1,343 | 886 (55 trained on) | 11,000 |

In all, 6% more training rows. Retrained, against the model before, on the same build:

| | before | retrained |
|---|---|---|
| offline, set.mm, first among 50 | 81.7% | 81.6% |
| set.mm, 1 s / 5 s | 83 / 101 | 81 / 98 |
| the compiler | 505 | 505 |
| mm0 | 230 | 230 |

- **No gain.** Every training theorem already has its known proof labelled at every node.
  Another proof of the same theorem adds labels of the same kind.
- **Found on the way:** one join ran for minutes past its 1 s (set.mm's theorem 5529, a
  product of 2·10¹¹ tuples), and 48 GB. Joins now look at the clock every 64 tuples.

### Step 4: the value of goals

**Setup:**
- **What it predicts:** how likely the search is to prove a goal. It is learned from the
  search's own trees, as GPT-f does.
- **Data:** every goal node of the trees `learned` grows in 1 s on every theorem, labelled
  1 if proved. A goal with metavariables counts only if its step was proved too. 3.3M rows.
- **Features:** 19, of the goal's expression and the theorem.
- **Model:** LightGBM, binary.
- **In search:** `learned(value=K)`. A step also costs K·Σ −ln V over its new goals, less
  that of the best of its goal's first variants. With `absolute=1`, not less.

**Offline:** AUC 0.83 on set.mm's test goals and 0.91 on mm0's, against 0.61 and 0.72 for
the best of three single features (size, `closable`, the weight of foreign symbols).

**In search,** every variant tried, on the test parts. The rows above `learned` with the
cap at ground goals ran on the build before that change; that row and those below it ran
on one build.

| variant | set.mm 1 s | set.mm 5 s | mm0 | compiler |
|---|---|---|---|---|
| `learned`, the old cap of premise-free steps | 83 | 101 | 230 | 505 |
| value v1 (proved = has a proof), absolute, K = 1, 2, 4 | 88, 88, 88 | 101 (K=2) | 146 (K=2) | 505 |
| v1, absolute, only on the steps above a leaf | 83 | | 228 | |
| value v2 (metavariable goals proved with their step), absolute, K = 1, 2, 4 | 86, 90, 91 | 104 (K=2) | 157 (K=2) | 505 |
| `learned`, premise-free steps capped at ground goals only | **84** | **104** | **230** | **505** |
| v2, absolute, K = 2, 4 | 89, 90 | **114** (K=2) | 179, 174 | 505 |
| v2, relative, K = 2, 4, 8 | 85, **88**, 86 | **107** (K=4) | 232, **230**, 231 | 505 (K=4) |
| v2, relative above the leaf and absolute at it, K = 2, 4 | 86, 84 | | 177, 172 | |

- **The relative value** (`value=4`) gains a little and loses nothing: +4 at 1 s, +3 at
  5 s. **The absolute one** (`value=2, absolute=1`) gains 10% on set.mm at 5 s and loses a
  fifth of mm0.
- **Goals with metavariables misled the first model.** A goal like `im ?1 (eq ?2 ?3)` is
  closed at once by the premise `im _G (eq …)`, so it always had a proof, and the value
  rated it 0.94. But the binding seldom suits the step's other goals. On mm0's
  `ASTIOeq1d` the search expanded 4,485 nodes instead of 62.
- **The cost of premise-free steps was wrong already.** At a bare goal `?0`, every
  assertion without premises fits, and all 3,351 were put one bucket after the rank's
  first, as if each proved its goal. That holds at ground goals only. Fixed, it helps
  `learned` alone: set.mm 104 at 5 s, against 101.
- **The absolute value loses mm0's long congruence chains** (`elabFmlaeq1d`, 13 steps,
  0.4 s without the value). Every step pays for goals that look hard, however good the
  step is. The leaf's own term does it: on the steps above alone it changes nothing, and
  the hybrid still loses mm0.
- **Open:** a value trained on the trees that the value itself grows; a value that sees
  the step's other goals, for goals with metavariables.

## 7. The tactics system: what the known proofs need (`DESIGN.md`, "The tactics system")

**Census of set.mm's 3.5M proof steps** by lemma family: 32% deduction-form bookkeeping
(`syl*`, `adant*`, `simp*`), 13% congruence, 6% chaining, 8% closure, 37% other. By the
shape of the step's conclusion: 34% a bare variable (the glue), 28% membership, 16%
equality, 8% biconditional, 3% a relation. The test theorems `learned` fails on have
proofs of 17 steps at the median (the proved ones 3); their most used lemmas are `a1i`
(6,315), `pire`, `adantr`, `syl`, `_2re`, `recnd`, `readdcld`: glue and the closure of ℝ.

**Scoped searches at the root** (`seq(bfs(filter=F, size=200000, depth=3), learned)`): 6
to 19 proved against 80. Not a measure of the scopes: the breadth-first prefix leaves
`learned` a tree of hundreds of expanded goals, and scoring each one's variants takes the
second. A sub-search belongs at the leaves, under a budget: `at($ pattern $, t, depth=N)`
was built for it.

**The subgoal bench** (`prove subgoals`): each statement of a step below the root of a
known proof, as the proof fixes it, is a task under the theorem's premises; the tactic gets
100 ms. set.mm's test part, 618 theorems, 6,436 determined subgoals:

| tactic | closed | depth 1 | depth 8+ | membership | equality | biconditional |
|---|---|---|---|---|---|---|
| `bfs` | 16% | 18% | 16% | 10% | 10% | 34% |
| `guided` | 51% | 28% | 66% | 59% | 50% | 48% |
| `learned` | **67%** | 45% | 80% | 76% | 63% | 63% |

`learned` closes 51% at 20 ms and 72% at 500 ms: five times the budget buys five points.
On peano `bfs` closes 68% and `guided` 74%; on mm0 `learned` 79%.

**The failed third,** by the kind of statement: 821 with quantifiers or binders (38% of
that kind fail), 801 the theorem's own matter (33%), 135 closure in ℝ/ℂ/ℕ (14%), 120
arithmetic identities under closure hypotheses (61%), 88 set algebra (28%), 43 numeral
arithmetic (25%), 41 propositional tautologies (21%), 37 iffs of arithmetic facts, 20
order facts. The decision procedures of the plan reach at most 484 subgoals, 7.5 points;
three quarters of the failures are the choice of lemmas and witnesses. The one kind the
search is bad at is arithmetic identities: `ring` first, `closure` not needed.

## 8. What the experiments say, together

- **Search is the engine's strength, and its reach is short:** unguided, 4 steps in a
  second. Everything that gained pushes it further along good paths: rails that close the
  goal (+54%), the learned rank (+52% over `guided`), the value of goals (+3% to +10%).
- **Learning from the files' own proofs works.** One model, trained once, serves every
  file. Learning from the search's own proofs added nothing in one round. Learning
  goal values from the search's trees added a little.
- **An LLM agent driving the engine step by step costs more than one writing MM1.** The
  agent's tokens follow its calls, and MM1's elaborator already does the unification. The
  engine as a gap filler did not pay either: the holes left are the hard steps.
- **The cheap decision is the one to delegate.** A model call costs microseconds and an
  LLM call costs a context. So the learned layer, not the LLM, is what should choose
  variants inside a search.
- **What remains hard:** long proofs whose steps all look ordinary (mm0's congruences),
  goals that are mostly metavariables, and arithmetic, which asks for decision procedures
  rather than search.
- **Search closes two thirds of the determined subgoals of real proofs in 100 ms,** and
  three quarters of the closure side conditions; decision procedures can add 7.5 points at
  most on set.mm's analysis part, `ring` being the one kind search is bad at. The failures
  that remain are binders and the theorem's own lemmas: the creative step.
