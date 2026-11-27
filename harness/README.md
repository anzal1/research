# Dot’s mathematical research harness

The harness runs three different searches, retains the exact scope of each result and times discovery separately from verification. Each problem has a mathematical reduction and a checker appropriate to its evidence. The Python searches use the standard library and run one at a time. Use a normal Python interpreter with assertions enabled.

```sh
python3 -B harness/run.py search
python3 -B harness/run.py all --json
python3 -B harness/run.py verify --problem quantum
python3 -B harness/run.py search --problem quantum --start-scale 209 --stop-scale 800
python3 -B harness/run.py search --problem shannon --shannon-removed 5
python3 -B harness/run.py search --problem euler --euler-bound 1000000
```

The first command starts each search from its inputs. Custom bounds let a researcher explore beyond the recorded run. Starting at 209 found another polynomial at scale 216 whose 70-step test passed. That extra candidate has no standalone Lean theorem here. The quantum search tries scales in numerical order. The Shannon search reads the published 367-word seed. The Euler search starts from the integer 1. The second command also regenerates the proof certificate, checks the first field by independent arithmetic, builds the quantum theorems and audits their axioms. It replays the Shannon neighborhood and independently checks the sixth-power bound. A failed audit gives a nonzero exit. JSON output contains timings and subprocess evidence for each phase. The Lean project pins Lean 4.24.0 and mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. [Lean setup](../lean-qutrit/README.md) · [Runner](run.py)

## Three targets

| Question and success criterion | Experiment | Outcome |
|---|---|---|
| For which even exponents h does a full-length Hermitian self-orthogonal extended Reed–Solomon code of dimension q−1 exist, with q = 2ʰ? Exhibit admissible weights and prove the code properties. | Split the input into a radius and one of five directions. Scan scalings of an element of order 29. Generate two polynomial certificates. | Scale 208 gives a second infinite family, beginning at q = 16,384. The earlier order-25 family begins at q = 1,024. [Proof and prior art](../lean-qutrit/Qmds/ORDER29.md) |
| Can 368 distinct five-symbol words survive a noisy seven-symbol channel without a single confused pair? One such code improves the published capacity lower bound. | Start with Polak and Schrijver’s 367 words. Remove at most four and try all ways to gain one. | Independent reproduction of a known exclusion. The longer five-deletion run also found none. A prior search reports coverage through fifteen. [Source and method](../shannon-seven/README.md) |
| Can five positive sixth powers sum to one positive sixth power? One exact identity settles existence. | Require one repeated pair, with four bases divisible by 42 and the remaining base coprime to 42. Bound the right-hand base by 500,000. | No identity in this subcase. Sorted residue classes and direct complementary-power lookup independently reproduce all 711 eligible pairs and 2,329 final tests. Both implementations also agree through 1,000,000, where 19,699 final tests gave zero identities. [Exact statement](../euler-sixth/README.md) |

On an Apple M5 Max with Python 3.9.6, one quiet run of the short searches took **0.504 s**, **1.576 s** and **3.722 s** respectively. These wall times include interpreter startup and exclude proof development, literature review and Lean verification. The five-deletion extension took 32.4 s including the thermal supervisor. A separate two-coordinate SAT search settled 21 previously unfinished projections on this branch in 39.3 s. All 343 projections for that coordinate pair returned UNSAT within budget. The [per-pair SAT results](../shannon-seven/radius-two-results.csv) include later runs. A first Lean build of the 70-step certificate took 25 min 26 s elapsed under thermal pacing, including about 15 min 6 s of CPU. The build then compiled the theorem connecting the certificate to the full code in 32 s. Both final declarations passed the axiom audit. Subsequent builds use Lake’s cache. Machine settings affect each timing. The second, more heavily paced run records the slower timings for the same searches. [Raw run outputs, timings and axiom audit](results.json)

## How to extend a search

Start with a dated primary source that specifies the question. Write down what object, counterexample or bound would change it. Choose a family small enough to explore exactly. Make the search return an inspectable witness or the precise boundary it exhausted. Check the winner in a representation independent of the search. For an infinite theorem, prove the reduction and connect the finite certificate to the original quantified statement. Record the exact declaration and its axiom audit. For a new adapter, add its commands to `run.py` and record the source, scope and success criterion in the table above.

Cinna Davis’s public post on Pomerance and Sárközy gives readers two competing predictions and links the argument. Her verification catalogue distinguishes written, partial and complete formal results. Elder Plinius’s public charter asks for a published definition and evidence a stranger can check. This project follows that evidence standard. Its three mathematical reductions were developed specifically for these problems. [Davis’s post](https://x.com/1337isnot1337/status/2126039890361979264) · [Davis’s verification records](https://itsdavis.com/solved-conjectures/docs/verification/) · [V3R1T4S charter](https://github.com/elder-plinius/V3R1T4S/blob/main/kit/CHARTER.md)
