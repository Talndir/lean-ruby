import tactic
import data.rel
import ruby.defs
import ruby.blocks
import ruby.rewrite1

open rel

variables {α β γ δ ε φ ψ : Type}

lemma sspp_eq_spss (r : rel α β) (s : rel β γ) (t : rel δ ε) (u : rel ε φ) (v : rel ψ (α × δ))
  : v ;; [r, t] ;; [s, u] = v ;; [r ;; s, t ;; u] :=
begin
  rw rel_seq_assoc,
  apply seq_cong_left,
  exact par_seq_dist r s t u,
end

lemma seq_lsh_seq_rsh (r : rel α ((β × γ) × δ))
  : r ;; lsh ;; rsh = r :=
begin
  rw [rel_seq_assoc, rsh_inv_left, seq_id_right],
end

--lemma seq_lsh_rsh : lsh ;; rsh = rsh ;; lsh := sorry

lemma seq_rsh_seq_lsh (r : rel α (β × (γ × δ)))
  : r ;; rsh ;; lsh = r :=
begin
  rw [rel_seq_assoc, rsh_inv_right, seq_id_right],
end

lemma seq_rsh_lsh_seq (r : rel (α × (β × γ)) δ)
  : rsh ;; lsh ;; r = r :=
begin
  rw [rsh_inv_right, seq_id_left],
end

lemma id_eq_rsh_lsh : idd = rsh ;; (@lsh α β γ)
  := rsh_inv_right.symm

lemma rel_seq_assoc' (r : rel α β) (s : rel β γ) (t : rel γ δ) :
  r ;; (s ;; t) = (r ;; s) ;; t := (comp_assoc r s t).symm

namespace tactic.interactive

meta def ruby_nf : tactic unit := `[
  simp only [
    sspp_eq_spss,
    seq_lsh_seq_rsh,
    seq_rsh_seq_lsh,
    seq_rsh_lsh_seq,
    id_eq_rsh_lsh,
    par_seq_dist,
    conv_par,
    conv_seq,
    conv_conv,
    rel_seq_assoc']
  ]

end tactic.interactive

example (r : rel (α × β) γ) (s : rel α δ) (t : rel γ ε)
  : (r† ;; [s, idd])† ;; t = (idd ;; [s†, idd]) ;; (r ;; t) :=
begin
  ruby_nf,
  sorry
end
