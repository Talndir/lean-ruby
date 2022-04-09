import tactic
import data.rel
import data.vector
import data.nat.basic
import ruby.defs

open rel vector nat

variables {α β γ δ ε φ ψ : Type}

/- Basic lemmas -/

--@[simp]
lemma rel_seq_assoc (r : rel α β) (s : rel β γ) (t : rel γ δ) :
  r ;; (s ;; t) = (r ;; s) ;; t := (comp_assoc r s t).symm

@[simp]
lemma seq_par_dist (r : rel α β) (s : rel β γ) (t : rel δ ε) (u : rel ε φ) :
  [r ;; s, t ;; u] = [r, t] ;; [s, u] :=
begin
  ext ⟨a,d⟩ ⟨c,f⟩,
  split,
  { rintro ⟨⟨b,rab,sbc⟩,⟨e,tde,uef⟩⟩,
    exact ⟨⟨b,e⟩,⟨⟨rab,tde⟩,⟨sbc,uef⟩⟩⟩, },
  { rintro ⟨⟨b,e⟩,⟨⟨rab,tde⟩,⟨sbc,uef⟩⟩⟩,
    exact ⟨⟨b,⟨rab,sbc⟩⟩,⟨e,⟨tde,uef⟩⟩⟩, }
end

@[simp]
lemma conv_seq (r : rel α β) (s : rel β γ) : (r ;; s)† = s† ;; r† := inv_comp r s

@[simp]
lemma conv_par (r : rel α β) (s : rel γ δ) : [r,s]† = [r†,s†] :=
begin
  ext ⟨b,d⟩ ⟨a,c⟩,
  split,
  { rintro ⟨rab,scd⟩,
    exact ⟨(inv_def r a b).mpr rab,(inv_def s c d).mpr scd⟩, },
  { rintro ⟨h1,h2⟩,
    simp at *,
    exact ⟨h1,h2⟩, }
end

@[simp]
lemma conv_conv (r : rel α β) : r†† = r := inv_inv r

@[simp]
lemma conv_id : (@idd α)† = @idd α := inv_id

@[simp]
lemma seq_id_left (r : rel α β) : idd ;; r = r := comp_left_id r

@[simp]
lemma seq_id_right (r : rel α β) : r ;; idd = r := comp_right_id r

@[simp]
lemma par_id : [idd, idd] = @idd (α × β) :=
begin
  ext ⟨a,b⟩ ⟨x,y⟩,
  split,
  rintro ⟨hax,hby⟩,
  simp * at *,
  intro h,
  exact ⟨congr_arg prod.fst h,congr_arg prod.snd h⟩,
end

lemma from_conv {r s : rel α β} : r† = s† ↔ r=s :=
begin
  split,
  { intro h,
    ext x y,
    unfold inv flip at h,
    have w := congr_fun (congr_fun h y) x, dsimp at w,
    simpa using w, },
  { intro h,
    rw h, }
end
