# NN-<concept-name>

> Copy this directory to author a new concept:
> `cp -r _TEMPLATE-concept NN-course/NN-name`, then fill in the four files and delete these quotes.

**Objective.** _One sentence: the capability or theorem this concept delivers._

**Prerequisites.** _Which earlier concepts / ideas you need first._

**The rung(s).** _If this is part of a ladder, list the steps. Otherwise "single rung."_

## Definition of done

- [ ] `make lab C=NN-course/NN-name` goes red → green (all `sorry`s discharged).
- [ ] `make test` stays green (Solution kernel-checks).
- [ ] `make axioms` clean (keystone depends only on accepted axioms).
- [ ] _(if anything graduates)_ verified code copied into `Principia/…`.

## Run

```bash
make lab C=NN-course/NN-name        # work the skeleton
make explainer C=NN-course/NN-name  # read the lesson
```
