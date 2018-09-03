Import Esub.Type.

Inductive guard :=
| GTrue
| GFalse
| GNot : guard -> guard
| GIf : guard -> guard -> guard -> guard.

