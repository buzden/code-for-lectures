Code is written in [Literate Idris](https://idris2.readthedocs.io/en/latest/reference/literate.html#embedding-in-markdown-like-documents),
so effectively, it is a compilable Markdown file.
Idris compiler supports compilation of Markdown files directly.
All compilable code is written in between
````
```idris
```
````
and
````
<!-- idris
-->
````

To compile and run this code, it's recommended to use [`pack` package manager](https://github.com/stefan-hoeck/idris2-pack/blob/main/INSTALL.md).

To build the code, run `pack build presentation`.
To run internal tests or the presentation, run `pack run presentation`.
