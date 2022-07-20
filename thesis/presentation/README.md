Report
===

The thesis presentation can be built locally using:

```
make thesis
```

It will create three files:
* `presentation-slides-only.pdf` (slides without notes)
* `presentation-slides-notes-dual.pdf` (slide on the left side, notes on the right)
* `presentation-slides-notes-interlaced.pdf` (slide on one page, notes on the next)

If you have `pympress` installed, you may use the following command to start the presentation:

```
pympress presentation-slides-notes-dual.pdf -t 30
```

The slides without notes are built by GitHub Actions on every commit push and the artifacts can be retrieved under the corresponding Actions workflow. Note that the artifacts expire after some time.
