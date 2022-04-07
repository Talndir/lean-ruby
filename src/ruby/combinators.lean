import tactic
import data.rel
import data.vector.basic
import data.nat.basic
import ruby.basic
import ruby.blocks
import ruby.tactics

open rel vector nat

variables {α β γ δ ε φ ψ : Type}


lemma seq_cong_right {r s : rel α β} {q : rel β γ} (h : r = s) : r ;; q = s ;; q := by rw h
lemma seq_cong_left {r s : rel β γ} {q : rel α β} (h : r = s) : q ;; r = q ;; s := by rw h


/- Fst and snd -/


abbreviation fst (r : rel α β) : rel (α × γ) (β × γ) := [r, idd]
abbreviation snd (r : rel α β) : rel (γ × α) (γ × β) := [idd, r]

lemma fst_eq (r : rel α β) {a : α} {b : β} {c d : γ} (h : (fst r) (a, c) (b, d)) : c = d := h.2
lemma snd_eq (r : rel α β) {a : α} {b : β} {c d : γ} (h : (snd r) (c, a) (d, b)) : c = d := h.1

lemma break_fst (r : rel α β) (s : rel β γ) : @fst α γ δ (r ;; s) = fst r ;; fst s
  := by simp [← seq_par_dist]

lemma break_snd (r : rel α β) (s : rel β γ) : @snd α γ δ (r ;; s) = snd r ;; snd s
  := by simp [← seq_par_dist]

@[simp]
lemma inv_fst (r : rel α β) : (fst r)† = @fst β α γ (r†) := by simp
@[simp]
lemma inv_snd (r : rel α β) : (snd r)† = @snd β α γ (r†) := by simp
@[simp]
lemma idd_fst : @fst α α β idd = idd := by { change [idd,idd] = idd, simp }
@[simp]
lemma idd_snd : @snd α α β idd = idd := by { change [idd,idd] = idd, simp }

lemma fst_snd_swap (r : rel α β)  (s : rel γ δ) : fst r ;; snd s = snd s ;; fst r :=
begin
  ext ⟨a,c⟩ ⟨b,d⟩,
  split,
  { rintro ⟨⟨x,y⟩,⟨⟨rax,h1⟩,⟨h2,syd⟩⟩⟩,
    use ⟨a,d⟩,
    simp * at *,
    exact ⟨⟨rfl,syd⟩,⟨rax,rfl⟩⟩, },
  { rintro ⟨⟨x,y⟩,⟨⟨h1,scy⟩,⟨rxb,h2⟩⟩⟩,
    use ⟨b,c⟩,
    simp * at *,
    exact ⟨⟨rxb,rfl⟩,⟨rfl,scy⟩⟩, }
end

lemma break_par (r : rel α β)  (s : rel γ δ) : [r, s] = fst r ;; snd s :=
begin
  ext ⟨a,c⟩ ⟨b,d⟩,
  split,
  rintro ⟨rab,scd⟩,
  use ⟨b,c⟩,
  exact ⟨⟨rab,rfl⟩,⟨rfl,scd⟩⟩,
  rintro ⟨⟨x,y⟩,⟨⟨rax,h1⟩,⟨h2,syd⟩⟩⟩,
  simp * at *,
  exact ⟨rax,syd⟩,
end

lemma break_par' (r : rel α β)  (s : rel γ δ) : [r, s] = snd s ;; fst r :=
begin
  rw ← fst_snd_swap r s,
  exact break_par r s,
end

/- Beside and below -/

def bes (r : rel (α × β) (δ × ψ)) (s : rel (ψ × γ) (ε × φ)) : rel (α × (β × γ)) ((δ × ε) × φ)
  := rsh ;; fst r ;; lsh ;; snd s ;; rsh

def bel (r : rel (α × ψ) (δ × ε)) (s : rel (β × γ) (ψ × φ)) : rel ((α × β) × γ) (δ × (ε × φ))
  := lsh ;; snd s ;; rsh ;; fst r ;; lsh

infixl `⟷`:70 := bes
infixl `↕`:70 := bel


/- Pow -/

def pow : rel α α → ℕ → rel α α
| r zero := idd
| r (succ n) := (pow r n) ;; r

instance rel_has_pow : has_pow (rel α α) ℕ :=
{ pow := pow }

def rel_pow_succ (r : rel α α) (n : ℕ) : r^(n+1) = r^n ;; r := rfl

@[simp]
lemma rel_pow_zero (r : rel α α) : r^0 = idd := rfl

@[simp]
lemma rel_pow_one (r : rel α α) : r^1 = r :=
begin
  change r^0 ;; r = r,
  simp,
end

@[simp]
lemma rel_pow_left (r : rel α α) (n : ℕ) : r ;; r^n = r^(n+1) :=
begin
  induction n with n hn,
  { simp, },
  { change r ;; (r^n ;; r) = r^(n+1) ;; r,
    rw ← hn,
    simp [rel_seq_assoc], }
end

@[simp]
lemma rel_pow_add (r : rel α α) (n m : ℕ) : r^n ;; r^m = r^(n+m) :=
begin
  induction m with m hm,
  { simp, },
  { change r^n ;; (r^m ;; r) = r^(n + m) ;; r,
    rw ← hm,
    simp [rel_seq_assoc], }
end


/- Map -/

def map : Π (n : ℕ), rel α β → rel (vector α n) (vector β n)
| zero r := nill
| (succ n) r := (apr n)† ;; [map n r, r] ;; apr n

lemma map_succ (r : rel α α) (n : ℕ) : map (n+1) r = (apr n)† ;; [map n r, r] ;; apr n := rfl

@[simp]
lemma rel_map_zero (r : rel α β) : map 0 r = nill := rfl

def map' : Π (n : ℕ), rel α β → rel (vector α n) (vector β n)
| zero r := nill
| (succ n) r := (apl n)† ;; [r, map' n r] ;; apl n

lemma map'_succ (r : rel α α) (n : ℕ) : map' (n+1) r = (apl n)† ;; [r, map' n r] ;; apl n := rfl

@[simp]
lemma rel_map'_zero (r : rel α β) : map' 0 r = nill := rfl


/- Tri -/

def tri : Π (n : ℕ), rel α α → rel (vector α n) (vector α n)
| zero r := nill
| (succ n) r := (apr n)† ;; [tri n r, r^n] ;; apr n

lemma tri_succ (r : rel α α) (n : ℕ) : tri (n+1) r = (apr n)† ;; [tri n r, r^n] ;; apr n := rfl

@[simp]
lemma tri_zero (r : rel α α) : tri 0 r = nill := rfl

theorem map_tri_comm (r : rel α α) (n : ℕ) : map n r ;; tri n r = tri n r ;; map n r :=
begin
  induction n with n hn,
  
  simp,

  have h : tri n.succ r;;map n.succ r = _;;[tri n r,r^n];;[map n r,r];;_,
  { calc tri n.succ r;;map n.succ r
      = _;;(apr n;;apr n†);;[map n r, r];;_ : by simp [map_succ, tri_succ, rel_seq_assoc]
  ... = _;;[tri n r,r^n];;[map n r,r];;_ : by simp [apr_inv_right] },
  
  calc map n.succ r;;tri n.succ r
      = _;;(apr n;;apr n†);;[tri n r,r ^ n];;_ : by simp [map_succ, tri_succ, rel_seq_assoc]
  ... = _;;([map n r,r];;[tri n r,r ^ n]);;_ : by simp [apr_inv_right, rel_seq_assoc]
  ... = _;;[tri n r ;; map n r,r^n;;r];;_ : by simp [← seq_par_dist, hn, rel_pow_succ]
  ... = tri n.succ r;;map n.succ r : by simp [h, rel_seq_assoc],

  /-
  { simp [map_succ, tri_succ],
    nth_rewrite 2 comp_assoc,
    nth_rewrite 5 comp_assoc,
    simp [apr_inv_right],
    nth_rewrite 1 comp_assoc,
    nth_rewrite 2 comp_assoc,
    simpa [← seq_par_dist, ← seq_par_dist, hn, rel_pow_left], }
  -/
end


def tri' : Π (n : ℕ), rel α α → rel (vector α n) (vector α n)
| zero r := nill
| (succ n) r := (apl n)† ;; [idd, tri' n r ;; map' n r] ;; apl n

lemma tri'_succ (r : rel α α) (n : ℕ) : tri' (n+1) r = (apl n)† ;; snd (tri' n r ;; map' n r) ;; apl n := rfl

@[simp]
lemma tri'_zero (r : rel α α) : tri' 0 r = nill := rfl

lemma map'_tri'_comm (r : rel α α) (n : ℕ) : map' n r ;; tri' n r = tri' n r ;; map' n r :=
begin
  induction n with n hn,
  simp,

  simp only [tri'_succ, map'_succ, assoc],
  apply seq_cong_left, repeat {rw ← assoc}, apply seq_cong_right,
  conv_lhs { l, arr, rw apl_inv_right, },
  conv_rhs { l, arr, rw apl_inv_right, },
  simp [← seq_par_dist, ← hn, assoc],
end

/-
lemma nil_append {n : ℕ} (xs : vector α n) : heq (append nil xs) xs :=
begin
  induction n with n hn,
  rw xs.eq_nil,
  simp,
  sorry
end

lemma splitvec {n : ℕ} (xs : vector α n) (x : α)
  : { v : α × vector α n | v.1 ::ᵥ v.2 = vector.append xs (x ::ᵥ nil) } :=
begin
  induction n with n hn,
  { rw xs.eq_nil,
    use ⟨x,nil⟩,
    dsimp,
    sorry, },
  sorry
end

theorem tri_eq_tri' (n : ℕ) (r : rel α α) : tri n r = tri' n r :=
begin
  induction n with n hn,
  simp,
  rw [tri_succ, tri'_succ, ← hn], clear hn,
  ext ps qs,
  split,
  { rintro ⟨⟨xs,x⟩,⟨⟨⟨ys,y⟩,⟨h1,⟨hl,hr⟩⟩⟩,h3⟩⟩,
    rcases splitvec xs x with ⟨⟨z,zs⟩,hz⟩,
    use ⟨z,zs⟩,
    unfold inv flip at h1 ⊢,
    rw apr_def at h3 h1,
    simp only [h3] at hz,
    refine ⟨_,hz⟩,
    rcases splitvec ys y with ⟨⟨w,ws⟩,hw⟩,
    use ⟨w,ws⟩,
    simp only [h1] at hw,
    dsimp,
    refine ⟨hw,_⟩,
    sorry },
  sorry
end
-/

/- Row -/

def row : Π (n : ℕ), rel (α × β) (γ × α) → rel (α × vector β n) (vector γ n × α)
| zero r := snd nill ;; @swap α (vector α 0) ;; fst nill
| (succ n) r := snd (apl n)† ;; (r ⟷ row n r) ;; fst (apl n)


def row_succ (n : ℕ) (r : rel (α × β) (γ × α))
  : row (n+1) r = snd (apl n)† ;; (r ⟷ row n r) ;; fst (apl n) := rfl


/- Reduce -/
/-
def rdl (n : ℕ) (r : rel (α × β) α) : rel (α × vector β n) α  
  := row n (r ;; (@π₂ α α)†) ;; π₂

@[simp]
lemma rdl_zero (r : rel (α × β) α) : rdl 0 r = π₁ :=
begin
  ext ⟨x,xs⟩ y,
  unfold rdl row snd fst idd,
  simp,
  split,
  { rintro ⟨⟨vs,v⟩,⟨⟨⟨zs,z⟩,⟨⟨⟨w,ws⟩,⟨⟨h1,-⟩,h3⟩⟩,⟨-,h5⟩⟩⟩,h2⟩⟩,
    simp only [and_true, swap_def, eq_iff_true_of_subsingleton] at h3,
    have h' : w = z := by simpa using h3,
    rw [h1, h', h5],
    simpa only [π₂_def] using h2, },
  { intro h,
    use ⟨nil,y⟩,
    simp only [and_true, π₂_def, eq_self_iff_true],
    use ⟨nil,y⟩,
    split, swap, exact ⟨nill_def,rfl⟩,
    use ⟨y,nil⟩,
    simp only [and_true, swap_def, eq_self_iff_true],
    rw xs.eq_nil,
    exact ⟨h,nill_def⟩, }
end
-/

def rdl : Π (n : ℕ), rel (α × β) α → rel (α × vector β n) α
| zero r := π₁
| (succ n) r := snd (apl n)† ;; rsh ;; fst r ;; rdl n r

def rdl_succ (n : ℕ) (r : rel (α × β) α) : rdl (n+1) r = snd (apl n)† ;; rsh ;; fst r ;; rdl n r := rfl

@[simp]
lemma rdl_zero (r : rel (α × β) α) : rdl 0 r = π₁ := rfl



def rdl' (n : ℕ) (r : rel (α × β) α) : rel (α × vector β n) α
  := row n (r ;; (@π₂ α α)†) ;; π₂

@[simp]
lemma rdl'_zero (r : rel (α × β) α) : rdl' 0 r = π₁ :=
begin
  ext ⟨x,xs⟩ y,
  unfold rdl' row,
  simp,
  split,
  { rintro ⟨⟨vs,v⟩,⟨⟨⟨zs,z⟩,⟨⟨⟨w,ws⟩,⟨⟨h1,-⟩,h3⟩⟩,⟨-,h5⟩⟩⟩,h2⟩⟩,
    simp * at *, },
  { intro h,
    use ⟨nil,y⟩,
    simp * at *,
    use ⟨nil,y⟩,
    split, swap, exact ⟨nill_def,rfl⟩,
    use ⟨y,nil⟩,
    simp only [and_true, swap_def, eq_self_iff_true],
    rw xs.eq_nil,
    exact ⟨rfl,nill_def⟩, }
end
