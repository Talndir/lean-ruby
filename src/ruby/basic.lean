import tactic
import data.rel
import data.vector
import data.nat.basic

open rel vector nat

variables {α β γ δ ε φ ψ : Type}

/- Basic defintions & notation -/

def par (r : rel α β) (s : rel γ δ) : rel (α × γ) (β × δ)
  := λ ⟨a,c⟩ ⟨b,d⟩, r a b ∧ s c d

infixl `;;`:60 := comp
notation `[` r `,` s `]` := par r s
postfix `†`:70 := inv

def conj (r : rel α α) (s : rel α β) : rel β β
  := s† ;; r ;; s

def conjt (r : rel (α × β) (β × α)) (s : rel β γ × rel α δ) : rel (δ × γ) (γ × δ)
  := [s.2†, s.1†] ;; r ;; [s.1, s.2]

infixl `\`:70 := conj
infixl `\\`:70 := conjt
notation `⟦` r `,` s `⟧` := ⟨r,s⟩

def stream (α : Type) : Type
  := ℤ → α

prefix `$`:100 := stream

def lift_to_stream (r : rel α β) : rel ($α) ($β)
  := λ a b, ∀ n, r (a n) (b n)

prefix `↟`:100 := lift_to_stream

@[simp]
def inv_def (r : rel α β) {a : α} {b : β} : r† b a ↔ r a b := by unfold inv flip

/- Making relations from functions -/

def idd : rel α α := eq

@[simp]
def idd_def (x y : α) : idd x y ↔ x = y := by unfold idd

instance fun_to_rel : has_coe (α → β) (rel α β) :=
{ coe := λ f x y, f x = y }

@[simp]
def to_rel (f : α → β) : rel α β
  := λ x y, f x = y

theorem conv_inv_left (r : rel α β) {f : α → β} {hr : r = to_rel f} {hs : function.surjective f} :
  r† ;; r = idd :=
begin
  ext x z,
  split,
  { rintro ⟨y,hxy,hyz⟩,
    simp [hr] at hxy hyz,
    simp [← hxy, ← hyz], },
  { intro h,
    simp at hr h,
    rw [hr, h],
    obtain ⟨y,hy⟩ := hs z,
    use y,
    simpa using hy, }
end

theorem conv_inv_right (r : rel α β) {f : α → β} {hr : r = to_rel f} {hi : function.injective f} :
  r ;; r† = idd :=
begin
  ext x z,
  unfold to_rel at hr,
  unfold idd inv flip,
  split,
  { rintro ⟨y,hxy,hyz⟩,
    rw hr at hxy hyz,
    rw ← hyz at hxy,
    exact hi hxy,
  },
  { intro h,
    rw [hr, h],
    unfold comp,
    use (f z),
    simp, }
end

theorem inv_left (r : rel α β) {f : α → β} {hr : r = to_rel f} {hf : function.bijective f} : r† ;; r = idd
  := @conv_inv_left _ _ r _ hr hf.2

theorem inv_right (r : rel α β) {f : α → β} {hr : r = to_rel f} {hf : function.bijective f} : r ;; r† = idd
  := @conv_inv_right _ _ r _ hr hf.1


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
