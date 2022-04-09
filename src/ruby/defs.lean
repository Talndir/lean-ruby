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

