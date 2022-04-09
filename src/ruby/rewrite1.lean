import tactic
import data.rel
import ruby.defs

open rel

variables {α β γ δ ε φ ψ : Type}

lemma seq_cong_right {r s : rel α β} {q : rel β γ} (h : r = s) : r ;; q = s ;; q := by rw h
lemma seq_cong_left {r s : rel β γ} {q : rel α β} (h : r = s) : q ;; r = q ;; s := by rw h

lemma par_seq_dist (r : rel α β) (s : rel β γ) (t : rel δ ε) (u : rel ε φ)
  : [r, t] ;; [s, u] = [r ;; s, t ;; u] :=
begin
  ext ⟨a,d⟩ ⟨c,f⟩,
  split,
  { rintro ⟨⟨b,e⟩,⟨⟨rab,tde⟩,⟨sbc,uef⟩⟩⟩,
    exact ⟨⟨b,⟨rab,sbc⟩⟩,⟨e,⟨tde,uef⟩⟩⟩, },
  { rintro ⟨⟨b,rab,sbc⟩,⟨e,tde,uef⟩⟩,
    exact ⟨⟨b,e⟩,⟨⟨rab,tde⟩,⟨sbc,uef⟩⟩⟩, },
end

lemma spsp_eq_spss (r : rel α β) (s : rel β γ) (t : rel δ ε) (u : rel ε φ) (v : rel (γ × φ) ψ)
  : [r, t] ;; [s, u] ;; v = [r ;; s, t ;; u] ;; v :=
begin
  apply seq_cong_right,
  exact par_seq_dist r s t u,
end

lemma conv_par (r : rel α β) (s : rel γ δ) : [r, s]† = [r†, s†] :=
begin
  ext ⟨b,d⟩ ⟨a,c⟩,
  split,
  { rintro ⟨rab,scd⟩,
    exact ⟨(inv_def r a b).mpr rab,(inv_def s c d).mpr scd⟩, },
  { rintro ⟨h1,h2⟩,
    simp at *,
    exact ⟨h1,h2⟩, }
end

lemma seq_id_left (r : rel α β) : idd ;; r = r := comp_left_id r

lemma seq_id_right (r : rel α β) : r ;; idd = r := comp_right_id r

lemma conv_id : (@idd α)† = @idd α := inv_id

lemma conv_seq (r : rel α β) (s : rel β γ) : (r ;; s)† = s† ;; r† := inv_comp r s

lemma conv_conv (r : rel α β) : r†† = r := inv_inv r

lemma rel_seq_assoc (r : rel α β) (s : rel β γ) (t : rel γ δ) :
  (r ;; s) ;; t = r ;; (s ;; t) := comp_assoc r s t


namespace tactic.interactive

meta def ruby_nf1 : tactic unit := `[
  simp only [
    par_seq_dist,
    spsp_eq_spss,
    conv_par,
    seq_id_left,
    seq_id_right,
    conv_id,
    conv_seq,
    conv_conv,
    rel_seq_assoc]
  ]

end tactic.interactive

example (r : rel (α × β) γ) (s : rel α δ) (t : rel γ ε)
  : (r† ;; [s, idd])† ;; t = (idd ;; [s†, idd]) ;; (r ;; t) := by ruby_nf1
