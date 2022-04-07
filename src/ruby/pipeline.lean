import tactic
import data.rel
import data.vector
import data.nat.basic
import ruby.combinators
import ruby.tactics

open rel vector nat

variables {α β γ δ ε φ ψ : Type}

lemma push_π₁ (r : rel α β) (p : rel γ δ) (hr : ∀ c : γ, ∃ d : δ, p c d) : [r, p] ;; π₁ = π₁ ;; r :=
begin
  ext ⟨x,y⟩ z,
  split,
  { rintro ⟨⟨b,d⟩,⟨⟨rxb,pyd⟩,h3⟩⟩,
    simp * at *,
    refine ⟨x,⟨by simp,rxb⟩⟩, },
  { rintro ⟨c,⟨h1,rcz⟩⟩,
    simp * at *,
    obtain ⟨w,pyw⟩ := hr y,
    use ⟨z,w⟩,
    simp * at *,
    exact ⟨rcz,pyw⟩, }
end

lemma push_π₂ (r : rel α β) (p : rel γ δ) (hr : ∀ a : α, ∃ b : β, r a b) : [r, p] ;; π₂ = π₂ ;; p :=
begin
  ext ⟨x,y⟩ z,
  split,
  { rintro ⟨⟨b,d⟩,⟨⟨rxb,pyd⟩,h3⟩⟩,
    simp * at *,
    refine ⟨y,⟨by simp,pyd⟩⟩, },
  { rintro ⟨c,⟨h1,pcz⟩⟩,
    simp * at *,
    obtain ⟨w,rxw⟩ := hr x,
    use ⟨w,z⟩,
    simp * at *,
    exact ⟨rxw,pcz⟩, }
end

def fun_to_exists (f : α → β) : ∀ a : α, ∃ b : β, (to_rel f) a b :=
begin
  intro a,
  use f a,
  simp,
end

lemma apl_proj {n : ℕ} : fst (apl n) ;; π₂ = @π₂ (β × vector β n) α
  := by simpa using push_π₂ (apl n) idd (fun_to_exists (apl_fun n))

lemma push_π₁_nill (r : rel α β) : [r, @nill γ δ] ;; π₁ = π₁ ;; r
  := push_π₁ r nill (begin intro c, use nil, end)

lemma push_rsh (r : rel α β) (s : rel γ δ) (t : rel ε φ) : [r, [s, t]] ;; rsh = rsh ;; [[r, s], t] :=
begin
  ext ⟨a,⟨c,e⟩⟩ ⟨⟨b,d⟩,f⟩,
  split,
  { rintro ⟨⟨b',⟨d',f'⟩⟩,⟨⟨hr,⟨hs,ht⟩⟩,h2⟩⟩,
    use ⟨⟨a,c⟩,e⟩,
    rw rsh_def at h2 ⊢,
    simp [← h2],
    exact ⟨⟨hr,hs⟩,ht⟩, },
  { rintro ⟨⟨⟨a',c'⟩,e'⟩,⟨h1,⟨⟨hr,hs⟩,ht⟩⟩⟩,
    use ⟨b,⟨d,f⟩⟩,
    rw rsh_def at h1 ⊢,
    simp [h1],
    exact ⟨hr,⟨hs,ht⟩⟩, }
end

lemma push_lsh (r : rel α β) (s : rel γ δ) (t : rel ε φ) : [[r, s], t] ;; lsh = lsh ;; [r, [s, t]] :=
begin
  apply from_conv.mp,
  unfold lsh, simp,
  exact (push_rsh (r†) (s†) (t†)).symm,
end

lemma horner_lemma (n : ℕ) (r : rel (α × β) α) (p : rel α α) (q : rel β β) (h : [p,q] ;; r = r ;; p)
  : [p, map' n q] ;; rdl n r = rdl n r ;; p :=
begin
  induction n with n hn,

  simpa using push_π₁_nill p,
  
  have h : rdl n.succ r;;p = [p,map' n.succ q];;rdl n.succ r,
  { calc rdl n.succ r;;p
      = _ ;; fst r ;; ([p, map' n q] ;; rdl n r) : by simp [rdl_succ, rel_seq_assoc, hn]
  ... = _ ;; (fst r ;; [p, map' n q]) ;; rdl n r : by simp [rel_seq_assoc]
  ... = _ ;; [r ;; p, map' n q] ;; _ : by simp [rel_seq_assoc, ← seq_par_dist]
  ... = _ ;; [[p,q] ;; r, map' n q] ;; _ : by rw h
  ... = _ ;; (rsh ;; [[p,q], map' n q]) ;; fst r ;; _ : by simp [← seq_par_dist, ← rel_seq_assoc]
  ... = snd (apl n)† ;; [p, [q, map' n q]] ;; rsh ;; _ : by simp [push_rsh, ← rel_seq_assoc]
  ... = [p, (apl n)† ;; [q, map' n q] ;; apl n] ;; snd (apl n)† ;; _ : by simp [← rel_seq_assoc, ← seq_par_dist, apl_inv_right]
  ... = [p, map' n.succ q] ;; rdl n.succ r : by simp [map'_succ, rdl_succ, rel_seq_assoc],
  },

  exact h.symm,
end

theorem horner (n : ℕ) (r : rel (α × β) α) (p : rel α α) (q : rel β β) (h : [p,q] ;; r = r ;; p)
  : snd (tri' n q) ;; rdl n (r ;; p) = rdl n r ;; p^n :=
begin
  induction n with n hn,

  simpa using push_π₁_nill idd,

  calc snd (tri' n.succ q) ;; rdl n.succ (r ;; p)
      = snd ((apl n)† ;; snd (tri' n q ;; map' n q) ;; apl n) ;; snd (apl n)† ;; rsh ;; fst (r ;; p) ;; rdl n (r ;; p) : by simp [tri'_succ, rdl_succ, rel_seq_assoc]
  ... = snd ((apl n)† ;; [idd, tri' n q ;; map' n q] ;; apl n) ;; _ : by simp [← rel_seq_assoc]
  ... = snd (apl n)† ;; snd (snd (tri' n q ;; map' n q)) ;; snd (apl n) ;; snd (apl n)† ;; rsh ;; fst (r ;; p) ;; _ : by simp [← seq_par_dist, rel_seq_assoc]
  ... = snd (apl n)† ;; snd (snd (tri' n q ;; map' n q)) ;; rsh ;; _ : by simp [← seq_par_dist, apl_inv_right, ← rel_seq_assoc]
  ... = snd (apl n)† ;; rsh ;; snd (tri' n q ;; map' n q) ;; fst (r ;; p) ;; _ : by simp [← rel_seq_assoc, push_rsh]
  ... = snd (apl n)† ;; rsh ;; [r ;; p, tri' n q ;; map' n q] ;; _ : by simp [← seq_par_dist, ← rel_seq_assoc]
  ... = snd (apl n)† ;; rsh ;; [r, tri' n q] ;; ([p, map' n q] ;; rdl n (r ;; p)) : by simp [← rel_seq_assoc]
  ... = snd (apl n)† ;; rsh ;; fst r ;; (snd (tri' n q) ;; rdl n (r ;; p)) ;; p : _
  ... = snd (apl n)† ;; rsh ;; fst r ;; rdl n r ;; (p^n ;; p) : by {rw hn, simp [rel_seq_assoc]}
  ... = snd (apl n)† ;; rsh ;; fst r ;; rdl n r ;; p^n.succ : by rw rel_pow_succ
  ... = rdl n.succ r ;; p^n.succ : by rw rdl_succ,

  { rw horner_lemma n (r ;; p) p q (begin rw rel_seq_assoc, exact seq_cong_right h, end),
    rw break_par,
    simp [rel_seq_assoc], },
end

theorem horner' (n : ℕ) (r : rel (α × β) α) (p : rel α α) (q : rel β β) (h : [p,q] ;; r = r ;; p)
  : snd (tri' n q) ;; rdl n (r ;; p) = rdl n r ;; p^n :=
begin
  induction n with n hn,

  simpa using push_π₁_nill idd,

  conv_lhs begin
    simp only [tri'_succ, rdl_succ, rel_seq_assoc, inv_snd],
    congr, congr, congr,
    simp [← break_snd, ← rel_seq_assoc, apl_inv_right],
    rw break_snd,
  end, conv_lhs begin
    simp [← rel_seq_assoc],
    congr, skip,
    rw [rel_seq_assoc, rel_seq_assoc], congr,
    simp [push_rsh, ← rel_seq_assoc, ← seq_par_dist],
    rw seq_par_dist,
  end, conv_lhs begin
    congr, skip, rw ← rel_seq_assoc, congr, skip,
    rw ← rel_seq_assoc,
    rw horner_lemma n (r ;; p) p q (begin rw rel_seq_assoc, exact seq_cong_right h, end),
    rw [rel_seq_assoc, break_par, ← rel_seq_assoc, ← rel_seq_assoc],
    congr, skip,
    rw [rel_seq_assoc, hn, ← rel_seq_assoc, ← rel_pow_succ],
  end,
  simp [rdl_succ, rel_seq_assoc],
end

theorem horner'' (n : ℕ) (r : rel (α × β) α) (p : rel α α) (q : rel β β) (h : [p,q] ;; r = r ;; p)
  : snd (tri' n q) ;; rdl n (r ;; p) = rdl n r ;; p^n :=
begin
  induction n with n hn,

  simpa using push_π₁_nill idd,

  simp only [tri'_succ, rdl_succ, rel_seq_assoc, inv_snd],
  conv_lhs { l, l, l, rw break_snd, ar, rw [← break_snd, apl_inv_right, break_snd], }, simp only [idd_snd, seq_id_right],
  conv_lhs { l, l, ar, rw push_rsh, }, simp only [par_id],
  conv_lhs { l, arr, arr, rw [← break_par', seq_par_dist, break_par], },
  conv_lhs { arr, arr, ar, 
     rw horner_lemma n (r ;; p) p q (by simpa [← assoc] using seq_cong_right h),
     all, arr, rw hn, },
  conv_lhs { r, r, arr, arr, rw ← rel_pow_succ, },
  repeat {rw assoc},
end

theorem horner2 (n : ℕ) (r : rel (α × β) α) (p : rel α α) (q : rel β β) (h : [p,q] ;; r = r ;; p)
  : snd (tri' n q) ;; rdl' n (r ;; p) = rdl' n r ;; p^n :=
begin
  induction n with n hn,
  simpa using push_π₁_nill idd,
  
  simp only [tri'_succ, rdl', row_succ, inv_snd, bes] at hn ⊢,
  --conv_lhs { rw [break_snd, break_snd], arr, all, all, all, rw [← break_snd, apl_inv_right] }, simp,
  conv_lhs { rw [break_snd, break_snd], ar, arr, 
    conv { r, all, all, all, rw [← break_snd, apl_inv_right], },
    rw [idd_snd], simp [← assoc], rw push_rsh, simp,
    conv { l, l, l, l, l, arr, rw [← fst_snd_swap], }, },


  sorry
end


lemma rel_inv_pow (r : rel α α) (h : r ;; r† = idd) {n : ℕ} : r^n ;; (r†)^n = idd :=
begin
  induction n with n hn,
  simp,
  rw [rel_pow_succ, ← rel_pow_left, rel_seq_assoc],
  nth_rewrite 1 ← rel_seq_assoc,
  simpa [h] using hn,
end

lemma push_delay (r : rel ($α × $β) ($α)) : [D, D] ;; r = r ;; D :=
begin
  ext ⟨x,y⟩ z,
  split,
  { rintro ⟨⟨a,b⟩,⟨⟨dxa,dyb⟩,rabz⟩⟩,
    use D_fun' z,
    refine ⟨_,D_fun_inv_right z⟩,
    unfold D to_rel D_fun at *,
    rw [← dxa, ← dyb] at rabz,
    sorry },
  {sorry}
end

theorem pipeline_reduce (n : ℕ) (r : rel ($α × $β) ($α))
  : snd (tri' n D) ;; rdl n (r ;; D) ;; (D†)^n = rdl n r :=
begin
  rw horner n r D D _,
  rw ← rel_seq_assoc,
  rw rel_inv_pow D D_inv_right,
  simp,
  { sorry },
end
