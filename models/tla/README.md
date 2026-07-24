# TLA+ temporal-liveness model of the DLC-D view-change protocol

`DlcdViewChange.tla` is the **temporal ◇** ("always eventually decides") that the
Tamarin view-change models (`models/tamarin/dlcd-viewchange{,-byz}.spthy`) cannot
express — those give *reachability* (progress is possible); this gives *inevitability*
under fairness. See `spec/bft-liveness-design.md` §4.

## What is checked

- **`Liveness == <>decided`** — under weak fairness on the decide / view-change actions
  (the GST "messages are eventually delivered" assumption), a decision is **eventually**
  reached. TLC-verified over the complete state space.
- **`DecidedStable`** — once decided, stays decided (stable agreement).
- **`TypeOK`** — type invariant.

The **partial-synchrony assumption is explicit and load-bearing**: the `ASSUME
\E v \in Views : v \notin FaultyViews` says leader rotation reaches a correct leader
(at most `f` of `n = 3f+1` are faulty). By FLP, liveness is impossible without it — and
the model is **non-vacuous**: an all-faulty config (`FaultyViews = {0,1,2}`) trips the
`ASSUME`, so liveness genuinely rests on the synchrony assumption. This is the honest
difference from ACP, whose TLA+ model-checks liveness *without* stating a synchrony
assumption (which FLP forbids universally).

## Run it

Needs a JRE. From the repo root:

```sh
bash scripts/check-tla.sh          # downloads tla2tools.jar on first run, runs TLC
```

Or directly (TLC 2.19+, `tla2tools.jar`):

```sh
cd models/tla
java -cp /path/to/tla2tools.jar tlc2.TLC -config DlcdViewChange.cfg DlcdViewChange.tla
```

Expected: `Model checking completed. No error has been found.` (config `MaxView = 2`,
`FaultyViews = {0}` — n=4/f=1, view 0's leader Byzantine, view 1 correct).

CI: `.github/workflows/tla.yml` installs a JRE and runs `scripts/check-tla.sh`.
