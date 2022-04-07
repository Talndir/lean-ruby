import tactic
import data.rel
import data.vector
import data.nat.basic
import ruby.basic

open rel vector nat

variables {α β γ δ ε φ : Type}


/- Delay-/

def D_fun (f : $α) : $α
  := λ n, f (n+1)

def D_fun' (f : $α) : $α
  := λ n, f (n-1)

lemma D_fun_inv_right (f : $α) : D_fun (D_fun' f) = f :=
begin
  unfold D_fun D_fun',
  simp,
end

lemma D_fun_inv_left (f : $α) : D_fun' (D_fun f) = f :=
begin
  unfold D_fun D_fun',
  simp,
end

def D : rel ($α) ($α)
  := to_rel D_fun

lemma D_inj : function.injective (@D_fun α) :=
begin
  intros f g h,
  ext x,
  have h' := congr_fun h (x-1),
  unfold D_fun at h',
  simpa using h',
end

lemma D_surj : function.surjective (@D_fun α) :=
begin
  intro f,
  use (λ n, f (n - 1)),
  unfold D_fun,
  simp,
end

lemma D_inv_left : (@D α)† ;; D = idd
  := @conv_inv_left ($α) ($α) D D_fun rfl D_surj

lemma D_inv_right : @D α ;; D† = idd
  := @conv_inv_right ($α) ($α) D D_fun rfl D_inj

/- Basics -/

def fork : rel α (α × α)
  := λ x ⟨y,z⟩, x=y ∧ x=z

def full : rel α β
  := λ x y, true

@[simp]
lemma full_def {a : α} {b : β} : full a b
  := by unfold full

def empt : rel α β
  := λ x y, false

def nill : rel (vector α 0) (vector β 0)
  := full

@[simp]
lemma nill_def {a : vector α 0} {b : vector β 0} : nill a b
  := by unfold nill

def π₁ : rel (α × β) α
  := to_rel prod.fst

@[simp]
lemma π₁_def {a c : α} {b : β} : π₁ (a, b) c ↔ a = c
  := by unfold π₁ to_rel prod.fst
 
def π₂ : rel (α × β) β
  := to_rel prod.snd

@[simp]
lemma π₂_def {a : α} {b c : β} : π₂ (a, b) c ↔ b = c
  := by unfold π₂ to_rel prod.snd


/- Left shift and right shift -/

def rsh_fun : α × (β × γ) → (α × β) × γ
  := λ ⟨x,⟨y,z⟩⟩, ⟨⟨x,y⟩,z⟩ 

def rsh : rel (α × (β × γ)) ((α × β) × γ)
  := to_rel rsh_fun

@[simp]
def rsh_def {a a' : α} {b b' : β} {c c' : γ} : rsh (a,(b,c)) ((a',b'),c') ↔ a=a' ∧ b=b' ∧ c=c' :=
begin
  unfold rsh to_rel rsh_fun,
  split, intro h,
  have ha : a = a' := congr_arg (prod.fst ∘ prod.fst) h,
  have hb : b = b' := congr_arg (prod.snd ∘ prod.fst) h,
  have hc : c = c' := congr_arg prod.snd h,
  exact ⟨ha,hb,hc⟩,
  rintro ⟨ha,hb,hc⟩,
  rwa [ha, hb, hc],
end

lemma rsh_inj : function.injective (@rsh_fun α β γ) :=
begin
  rintro ⟨a,⟨b,c⟩⟩ ⟨x,⟨y,z⟩⟩ h,
  unfold rsh_fun at h,
  simp at *,
  tauto,
end

lemma rsh_surj : function.surjective (@rsh_fun α β γ) :=
begin
  rintro ⟨⟨a,b⟩,c⟩,
  use ⟨a,⟨b,c⟩⟩,
  refl,
end

lemma rsh_inv_left : (@rsh α β γ)† ;; rsh = idd
  := @conv_inv_left (α × (β × γ)) ((α × β) × γ) rsh rsh_fun rfl rsh_surj

lemma rsh_inv_right : @rsh α β γ ;; rsh† = idd
  := @conv_inv_right (α × (β × γ)) ((α × β) × γ) rsh rsh_fun rfl rsh_inj

def lsh : rel ((α × β) × γ) (α × (β × γ)) := rsh†


/- Swap -/

def swap : rel (α × β) (β × α)
  := to_rel prod.swap

@[simp]
lemma swap_def {a d : α} {b c : β} : swap (a,b) (c,d) ↔ a=d ∧ b=c :=
begin
  unfold swap to_rel prod.swap,
  simp only [prod.mk.inj_iff, and.comm],
end

lemma swap_inv_left : (@swap α β)† ;; swap = idd
  := @conv_inv_left (α × β) (β × α) swap prod.swap rfl prod.swap_surjective

lemma swap_inv_right : @swap α β ;; swap† = idd
  := @conv_inv_right (α × β) (β × α) swap prod.swap rfl prod.swap_injective


/- Fork2 -/

def fork2 : rel (α × α) ((α × β) × β)
  := π₁† ;; [ fork† , fork ] ;; rsh


/- Append right and append left -/

def apr_fun (n : ℕ) : vector α n × α → vector α (n+1)
  := λ ⟨xs,x⟩, xs.append (x ::ᵥ nil)

def apr (n : ℕ) : rel (vector α n × α) (vector α (n+1))
  := to_rel (apr_fun n)

@[simp]
def apr_def {n : ℕ} {xs : vector α n} {x : α} {ys : vector α (n+1)} : apr n (xs,x) ys ↔ append xs (x ::ᵥ nil) = ys
  := by unfold apr to_rel apr_fun

lemma apr_inj (n : ℕ) : function.injective (@apr_fun α n) :=
begin
  rintro ⟨xs,x⟩ ⟨ys,y⟩ h,
  unfold apr_fun at h,
  sorry
end

lemma apr_inv_right (n : ℕ) : (@apr α n ;; (apr n)†) = idd
  := @conv_inv_right (vector α n × α) (vector α (n+1)) (apr n) (apr_fun n) rfl (apr_inj n)

def apl_fun (n : ℕ) : α × vector α n → vector α (n+1)
  := λ ⟨x,xs⟩, x ::ᵥ xs

def apl (n : ℕ) : rel (α × vector α n) (vector α (n+1))
  := to_rel (apl_fun n)

@[simp]
def apl_def {n : ℕ} {x : α} {xs : vector α n} {ys : vector α (n+1)} : apl n (x,xs) ys ↔ (x ::ᵥ xs) = ys
  := by unfold apl to_rel apl_fun

lemma apl_inv_right (n : ℕ) : (@apl α n ;; (apl n)†) = idd
  := sorry--@conv_inv_right (vector α n × α) (vector α (n+1)) (apr n) (apr_fun n) rfl (apr_inj n)
