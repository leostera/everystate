Medians of 5 runs per cell. Ratio = base / build (above 1: faster than base).

- `bench/search/large5.json`: 2026-11-26T03:14:10.990Z, harness e1cf1ce+dirty; builds base=28fd7c5, hashcons=afa9e05, idcache=db119b1, parallel=e1cf1ce

### 1 worker

| model | distinct | base wall s | base CPU s | base RSS MB | hashcons wall s | wall ratio | hashcons CPU s | CPU ratio | hashcons RSS MB | idcache wall s | wall ratio | idcache CPU s | CPU ratio | idcache RSS MB | parallel wall s | wall ratio | parallel CPU s | CPU ratio | parallel RSS MB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| OrSet-fixed-f1 | 129,242 | 0.488 | 0.486 | 82 | 0.506 | 0.97x | 0.503 | 0.97x | 31 | 0.200 | 2.44x | 0.197 | 2.46x | 24 | 0.202 | 2.41x | 0.200 | 2.43x | 24 |
| OrSet-fixed-f4 | 524,832 | 2.04 | 2.04 | 314 | 2.16 | 0.94x | 2.16 | 0.94x | 133 | 0.733 | 2.78x | 0.731 | 2.78x | 83 | 0.764 | 2.67x | 0.761 | 2.67x | 86 |
| ReadRepair-fixed-f6 | 383,579 | 1.70 | 1.69 | 204 | 1.93 | 0.88x | 1.93 | 0.88x | 100 | 0.876 | 1.94x | 0.873 | 1.94x | 61 | 0.866 | 1.96x | 0.861 | 1.97x | 59 |
| LostUpdate-fixed-f6 | 420,646 | 1.38 | 1.38 | 201 | 1.51 | 0.91x | 1.51 | 0.91x | 114 | 0.646 | 2.13x | 0.644 | 2.14x | 55 | 0.679 | 2.03x | 0.676 | 2.03x | 55 |
| LeaseLock-fixed-f5 | 122,728 | 0.410 | 0.408 | 68 | 0.455 | 0.90x | 0.453 | 0.90x | 36 | 0.201 | 2.04x | 0.197 | 2.07x | 25 | 0.207 | 1.98x | 0.205 | 1.99x | 25 |
| **total** |  | 6.01 | 6.00 |  | 6.57 | 0.92x | 6.55 | 0.92x |  | 2.66 | 2.26x | 2.64 | 2.27x |  | 2.72 | 2.21x | 2.70 | 2.22x |  |

### 8 workers

| model | distinct | base wall s | base CPU s | base RSS MB | hashcons wall s | wall ratio | hashcons CPU s | CPU ratio | hashcons RSS MB | idcache wall s | wall ratio | idcache CPU s | CPU ratio | idcache RSS MB | parallel wall s | wall ratio | parallel CPU s | CPU ratio | parallel RSS MB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| OrSet-fixed-f1 | 129,242 | 0.182 | 0.709 | 121 | 0.273 | 0.67x | 1.36 | 0.52x | 108 | 0.183 | 0.99x | 0.878 | 0.81x | 155 | 0.080 | 2.28x | 0.455 | 1.56x | 155 |
| OrSet-fixed-f4 | 524,832 | 0.528 | 3.18 | 313 | 1.12 | 0.47x | 7.74 | 0.41x | 311 | 0.637 | 0.83x | 3.51 | 0.91x | 359 | 0.237 | 2.23x | 1.59 | 2.00x | 326 |
| ReadRepair-fixed-f6 | 383,579 | 0.386 | 2.28 | 209 | 0.562 | 0.69x | 3.61 | 0.63x | 206 | 0.399 | 0.97x | 2.06 | 1.11x | 246 | 0.201 | 1.92x | 1.42 | 1.61x | 231 |
| LostUpdate-fixed-f6 | 420,646 | 0.320 | 1.76 | 160 | 0.440 | 0.73x | 2.66 | 0.66x | 152 | 0.303 | 1.06x | 1.68 | 1.05x | 200 | 0.175 | 1.83x | 1.21 | 1.46x | 191 |
| LeaseLock-fixed-f5 | 122,728 | 0.141 | 0.522 | 74 | 0.181 | 0.78x | 0.768 | 0.68x | 69 | 0.134 | 1.05x | 0.506 | 1.03x | 112 | 0.064 | 2.20x | 0.380 | 1.37x | 104 |
| **total** |  | 1.56 | 8.45 |  | 2.58 | 0.60x | 16.13 | 0.52x |  | 1.66 | 0.94x | 8.63 | 0.98x |  | 0.757 | 2.06x | 5.05 | 1.67x |  |

