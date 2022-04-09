import tactic
import ruby.rewrite1

open rel

variables {α β γ δ ε φ ψ : Type}

--set_option trace.app_builder true

example (r : rel (α × β) γ) (s : rel α δ) (t : rel γ ε)
  : (r† ;; [s, idd])† ;; t = (idd ;; [s†, idd] ;; r) ;; t := by ruby_nf
