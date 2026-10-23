# The learned models of the front-ends

The MCP server (`mm0-whitehead mcp`) and the gap filler (`prove goal`) read these by
default (`--models DIR` names another directory, `--no-models` reads none; `--model`,
`--cheap` and `--value` name single files). They are the best setting of the bench on
2026-10-22 (`docs/STATUS.md`; `docs/EXPERIMENTS.md`, "More negatives, drawn evenly"):
set.mm's test theorems, every 10th from the last tenth, 104 of 618 proved at 1 s and 128
at 5 s with `learned(value=4)`.

| file | what | trained as |
|---|---|---|
| `ranker.json` | the rank of a goal's variants (`by=model`): LightGBM lambdarank, 100 trees of `featureNames` | `m6`: `learn/train.py --sample-train 0.3 --weights sqrt`, the data of `prove export` for every file of the corpus plus every 3rd training and tuning theorem of set.mm, hello_mmc and mm0 with 200 negatives a node |
| `cheap.json` | the first stage of the rank (`--cheap`): 10 trees of the features that need no instantiation of the variant's new goals; it orders all the variants, the ranker the first `top` (128) | `cheap6`: the same data, `--zero` on the other ten features |
| `value.json` | the value of goals (`value=K`): a binary model, 100 trees of `goalFeatureNames` | `v4`: `learn/train_value.py` on the goal rows of 1 s searches with the ranker `m3` (`prove export --search learned --goals`) |

A model names its features; the program refuses one whose features are not the first of
its own, in their order (`Model.load`): a model trained before a feature was added still
reads, the later features unread. These three were trained on the 30 features before the
contexts of use (`ctx_pos`, `ctx_neg`, `ctx_rival`, 2026-10-23) and read none of them;
retrain after a change of an existing feature of `featureNames` or `goalFeatureNames`.
