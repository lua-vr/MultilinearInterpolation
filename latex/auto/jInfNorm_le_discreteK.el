;; -*- lexical-binding: t; -*-

(TeX-add-style-hook
 "jInfNorm_le_discreteK"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "11pt")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("amsmath" "") ("amssymb" "") ("amsthm" "") ("geometry" "margin=2.8cm")))
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art11"
    "amsmath"
    "amssymb"
    "amsthm"
    "geometry")
   (TeX-add-symbols
    '("norm" 2)
    '("abs" 1)
    "cJ"
    "Z"
    "W")
   (LaTeX-add-labels
    "eq:abs-add"
    "thm:main"
    "lem:K-dyadic"
    "lem:near-opt"
    "lem:lq-max"
    "prop:split"
    "eq:inv"
    "eq:step"
    "lem:pointwise"
    "eq:near-opt"
    "eq:weighted"
    "rem:other-constant")
   (LaTeX-add-amsthm-newtheorems
    "theorem"
    "proposition"
    "lemma"
    "definition"
    "remark"))
 :latex)

