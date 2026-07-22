import VersoManual.Bibliography
import VersoBlueprint.Cite

open Verso.Genre Manual Informal Bibliography

@[bib "janson"]
def janson : Citable := .article
  { title := inlines!"On interpolation of multi-linear operators"
  , authors := #[inlines!"S. Janson"]
  , journal := inlines!"Function Spaces and Applications"
  , year := 1988
  , month := .none
  , volume := inlines!"1302"
  , number := .empty
  , pages := some (290, 302)
  }
