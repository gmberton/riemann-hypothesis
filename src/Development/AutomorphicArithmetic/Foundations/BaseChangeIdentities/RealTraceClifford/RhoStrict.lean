module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll

@[expose] public section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private def dM {n : ℕ} (x : Wt n) : ℝ := ∑ a, ∑ b, (x a - x b) ^ 2

private theorem dM_nonneg {n : ℕ} (x : Wt n) : 0 ≤ dM x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem dM_perm {n : ℕ} (x : Wt n) (w : Equiv.Perm (Fin n)) : dM (x ∘ w) = dM x := by
  unfold dM
  calc ∑ a, ∑ b, ((x ∘ w) a - (x ∘ w) b) ^ 2 = ∑ a, ∑ b, (x (w a) - x b) ^ 2 :=
        Finset.sum_congr rfl fun a _ => Equiv.sum_comp w (fun b => (x (w a) - x b) ^ 2)
    _ = ∑ a, ∑ b, (x a - x b) ^ 2 := Equiv.sum_comp w (fun a => ∑ b, (x a - x b) ^ 2)

private theorem dM_eq {n : ℕ} (x : Wt n) :
    dM x = 2 * n * ∑ a, x a ^ 2 - 2 * (∑ a, x a) ^ 2 := by
  have h : ∀ a, ∑ b, (x a - x b) ^ 2 = n * x a ^ 2 - 2 * x a * (∑ b, x b) + ∑ b, x b ^ 2 := by
    intro a
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold dM
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

private theorem dM_nat {n : ℕ} (x : Wt n) (h : ∀ a b, ∃ m : ℤ, x a - x b = m) :
    ∃ k : ℕ, dM x = k := by
  choose m hm using h
  have h1 : dM x = ((∑ a, ∑ b, (m a b) ^ 2 : ℤ) : ℝ) := by
    simp [dM, hm]
  have h0 : 0 ≤ ∑ a, ∑ b, (m a b) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h0
  exact ⟨k, by rw [h1, hk]; simp⟩

private theorem dom_int {n : ℕ} {x : Wt n} (h : Dom x) (a b : Fin n) :
    ∃ m : ℤ, x a - x b = m := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨m, hm⟩ := h a b hab
    exact ⟨m, by simp [hm]⟩
  · exact ⟨0, by simp⟩
  · obtain ⟨m, hm⟩ := h b a hab
    exact ⟨-m, by push_cast; linarith⟩

private theorem rho_strict {n : ℕ} {κ : Wt n} (hκ : Antitone κ) (w : Equiv.Perm (Fin n))
    (hne : κ ∘ w ≠ κ) : ∑ a, rhoV n a * (κ ∘ w) a < ∑ a, rhoV n a * κ a := by
  obtain ⟨-, hdom, hanti, -, -, -⟩ := rearr n
  refine (hanti.antitone.monovary hκ).sum_mul_comp_perm_lt_sum_mul_iff.2 fun hM => hne ?_
  have hu : Antitone (κ ∘ w) := fun a b hab => not_lt.1 fun hlt =>
    absurd (hM hlt) (not_le.2 (hanti (hab.lt_of_ne fun h => hlt.ne (congrArg (κ ∘ w) h))))
  rw [← (hdom (κ ∘ w)).2.2.1 hu, (hdom κ).2.2.2.1 w, (hdom κ).2.2.1 hκ]

private theorem dM_lt {n : ℕ} {κ : Wt n} (hκ : Antitone κ) (w : Equiv.Perm (Fin n))
    (hne : κ ∘ w ≠ κ) : dM (κ ∘ w + rhoV n) < dM (κ + rhoV n) := by
  have hs := rho_strict hκ w hne
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hs
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : ∑ a, (κ ∘ w) a = ∑ a, κ a := Equiv.sum_comp w κ
  have e2 : ∑ a, (κ ∘ w) a ^ 2 = ∑ a, κ a ^ 2 := Equiv.sum_comp w (fun a => κ a ^ 2)
  have q : ∀ u : Wt n, ∑ a, (u + rhoV n) a ^ 2 =
      ∑ a, u a ^ 2 + 2 * ∑ a, rhoV n a * u a + ∑ a, rhoV n a ^ 2 := by
    intro u
    simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun a _ => by ring
  have l : ∀ u : Wt n, ∑ a, (u + rhoV n) a = ∑ a, u a + ∑ a, rhoV n a := by
    intro u
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [dM_eq, dM_eq, q, q, l, l, e1, e2]
  have := mul_lt_mul_of_pos_left hs hnR
  nlinarith

private theorem dom_sub {n : ℕ} {x : Wt n} (hx : StrictAnti x)
    (hi : ∀ a b, ∃ m : ℤ, x a - x b = m) : Dom (x - rhoV n) := by
  obtain ⟨-, hdom, -, -, hDD, -⟩ := rearr n
  have hD : Dom x := fun a b hab => by
    obtain ⟨m, hm⟩ := hi a b
    have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast (sub_pos.2 (hx hab)).le.trans_eq hm
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hm0
    exact ⟨k, by rw [hm, hk]; simp⟩
  have ha : Antitone (x - rhoV n) := by
    cases n with
    | zero => exact fun a => a.elim0
    | succ n =>
      refine Fin.antitone_iff_succ_le.2 fun i => ?_
      obtain ⟨m, hm⟩ := hi i.castSucc i.succ
      have hm0 : (0 : ℤ) < m := by exact_mod_cast (sub_pos.2 (hx i.castSucc_lt_succ)).trans_eq hm
      have h1 : (1 : ℝ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
      simp only [Pi.sub_apply, rhoV, Fin.val_succ, Fin.val_castSucc]
      push_cast
      linarith
  have h2 := (hDD x hD).2
  rwa [(hdom (x - rhoV n)).2.2.1 ha] at h2

private theorem cf_sum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → FR n) (x : Wt n) :
    cf (∑ i ∈ s, f i) x = ∑ i ∈ s, cf (f i) x := by
  simp [cf, Finsupp.finsetSum_apply]

private theorem sym_add {n : ℕ} {f g : FR n} (hf : Sym f) (hg : Sym g) : Sym (f + g) := fun w x => by
  rw [((cfBasic n).2.2.2.1 f g 0 _).1, ((cfBasic n).2.2.2.1 f g 0 x).1, hf, hg]

private theorem sym_smul {n : ℕ} {f : FR n} (c : ℂ) (hf : Sym f) : Sym (c • f) := fun w x => by
  rw [((cfBasic n).2.2.2.1 f f c _).2, ((cfBasic n).2.2.2.1 f f c x).2, hf]

private theorem sym_sum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → FR n) (h : ∀ i ∈ s, Sym (f i)) :
    Sym (∑ i ∈ s, f i) := fun w x => by
  rw [cf_sum, cf_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi w x

private theorem sym_orbit {n : ℕ} (κ : Wt n) : Sym (∑ w : Equiv.Perm (Fin n), ex (κ ∘ w)) := by
  classical
  intro v x
  rw [cf_sum, cf_sum]
  simp only [cf, ex, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [← Equiv.sum_comp (Equiv.mulRight v⁻¹) (fun w : Equiv.Perm (Fin n) => if κ ∘ w = x then (1 : ℂ) else 0)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : (κ ∘ w = x ∘ v) ↔ (κ ∘ (Equiv.mulRight v⁻¹ w) = x) := by
    constructor
    · intro h
      funext b
      have := congrFun h (v⁻¹ b)
      simpa using this
    · intro h
      funext a
      have := congrFun h (v a)
      simpa using this
  simp only [this]

private theorem alt_orbit {n : ℕ} (κ : Wt n) :
    alt (rhoV n) * ∑ w : Equiv.Perm (Fin n), ex (κ ∘ w) =
      ∑ w : Equiv.Perm (Fin n), alt (κ ∘ w + rhoV n) := by
  have hadd := (cfBasic n).1
  calc alt (rhoV n) * ∑ w : Equiv.Perm (Fin n), ex (κ ∘ w)
      = ∑ v : Equiv.Perm (Fin n), ∑ w : Equiv.Perm (Fin n),
          sg v • (ex (rhoV n ∘ v) * ex (κ ∘ w)) := by
        simp only [alt, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc]
        rw [Finset.sum_comm]
    _ = ∑ v : Equiv.Perm (Fin n), ∑ w : Equiv.Perm (Fin n),
          sg v • (ex (rhoV n ∘ v) * ex (κ ∘ (w * v : Equiv.Perm (Fin n)))) :=
        Finset.sum_congr rfl fun v _ => (Equiv.sum_comp (Equiv.mulRight v)
          (fun w : Equiv.Perm (Fin n) => sg v • (ex (rhoV n ∘ v) * ex (κ ∘ w)))).symm
    _ = ∑ w : Equiv.Perm (Fin n), alt (κ ∘ w + rhoV n) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp only [alt]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← hadd]
        congr 2
        ext a
        simp [add_comm]

private theorem step {n N : ℕ}
    (ih : ∀ κ : Wt n, Dom κ → dM (κ + rhoV n) < N →
      ∃ χ : FR n, Sym χ ∧ alt (rhoV n) * χ = alt (κ + rhoV n))
    (z : Wt n) (hi : ∀ a b, ∃ m : ℤ, z a - z b = m) (hz : dM z < N) :
    ∃ χ : FR n, Sym χ ∧ alt (rhoV n) * χ = alt z := by
  by_cases hinj : Function.Injective z
  · obtain ⟨-, hdom, -, -, -, -⟩ := rearr n
    obtain ⟨han, ⟨u, hu⟩, -⟩ := hdom z
    have hs : StrictAnti (domC z) :=
      han.strictAnti_of_injective (by rw [hu]; exact hinj.comp u.injective)
    have hi' : ∀ a b, ∃ m : ℤ, domC z a - domC z b = m := by
      intro a b
      rw [hu]
      exact hi _ _
    have hD := dom_sub hs hi'
    have hlt : dM (domC z - rhoV n + rhoV n) < N := by
      rw [sub_add_cancel, hu, dM_perm]
      exact hz
    obtain ⟨χ, hS, hχ⟩ := ih _ hD hlt
    rw [sub_add_cancel, hu, (cfBasic n).2.2.2.2.2.2.2.1 z u] at hχ
    refine ⟨sg u • χ, sym_smul _ hS, ?_⟩
    have hsg : sg u * sg u = 1 := by
      unfold sg; rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
    rw [mul_smul_comm, hχ, smul_smul, hsg, one_smul]
  · refine ⟨0, fun _ _ => rfl, ?_⟩
    rw [mul_zero, (cfBasic n).2.2.2.2.2.2.2.2.2.2.2.2 z hinj]

theorem UpperTheory.RealTr.divEx :
    ∀ (n : ℕ) (κ : Wt n), Dom κ → ∃ χ : FR n, Sym χ ∧ alt (rhoV n) * χ = alt (κ + rhoV n) := by
  classical
  intro n
  obtain ⟨-, -, -, hDρ, hDD, -⟩ := rearr n
  have hint : ∀ κ : Wt n, Dom κ → ∀ (w : Equiv.Perm (Fin n)) a b,
      ∃ m : ℤ, (κ ∘ w + rhoV n) a - (κ ∘ w + rhoV n) b = m := by
    intro κ hκ w a b
    obtain ⟨m, hm⟩ := dom_int hκ (w a) (w b)
    obtain ⟨m', hm'⟩ := dom_int hDρ a b
    refine ⟨m + m', ?_⟩
    simp only [Pi.add_apply, Function.comp]
    push_cast
    linarith
  have main : ∀ N : ℕ, ∀ κ : Wt n, Dom κ → dM (κ + rhoV n) < N →
      ∃ χ : FR n, Sym χ ∧ alt (rhoV n) * χ = alt (κ + rhoV n) := by
    intro N
    induction N with
    | zero =>
      intro κ _ h
      exact absurd h (by simpa using dM_nonneg _)
    | succ N ih =>
      intro κ hκ hlt
      have hanti := (hDD κ hκ).1
      obtain ⟨k, hk⟩ := dM_nat (κ ∘ (1 : Equiv.Perm (Fin n)) + rhoV n) (hint κ hκ 1)
      have hk' : dM (κ + rhoV n) = k := hk
      have hterm : ∀ w : Equiv.Perm (Fin n), κ ∘ w ≠ κ →
          ∃ χ : FR n, Sym χ ∧ alt (rhoV n) * χ = alt (κ ∘ w + rhoV n) := by
        intro w hw
        refine step ih _ (hint κ hκ w) ?_
        obtain ⟨k', hk''⟩ := dM_nat _ (hint κ hκ w)
        have h1 := dM_lt hanti w hw
        rw [hk'', hk'] at h1
        rw [hk'] at hlt
        rw [hk'']
        have h2 : k' < k := by exact_mod_cast h1
        have h3 : k < N + 1 := by exact_mod_cast hlt
        exact_mod_cast (by omega : k' < N)
      choose! χ hχS hχ using hterm
      set S : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter (fun w => κ ∘ w = κ) with hS
      have hc : ((S.card : ℂ)) ≠ 0 := by
        have : 0 < S.card := Finset.card_pos.2 ⟨1, by simp [hS]⟩
        exact_mod_cast this.ne'
      set T : FR n := ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ¬ κ ∘ w = κ), χ w with hT
      refine ⟨(S.card : ℂ)⁻¹ • ((∑ w : Equiv.Perm (Fin n), ex (κ ∘ w)) + (-1 : ℂ) • T),
        sym_smul _ (sym_add (sym_orbit κ) (sym_smul _ (sym_sum _ _ fun w hw => hχS w (by simpa using hw)))), ?_⟩
      have e1 : alt (rhoV n) * T =
          ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ¬ κ ∘ w = κ), alt (κ ∘ w + rhoV n) := by
        rw [hT, Finset.mul_sum]
        exact Finset.sum_congr rfl fun w hw => hχ w (by simpa using hw)
      have e2 : ∑ w ∈ S, alt (κ ∘ w + rhoV n) = (S.card : ℂ) • alt (κ + rhoV n) := by
        have : ∀ w ∈ S, alt (κ ∘ w + rhoV n) = alt (κ + rhoV n) := fun w hw => by
          rw [(Finset.mem_filter.1 hw).2]
        rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.cast_smul_eq_nsmul]
      have e3 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun w : Equiv.Perm (Fin n) => κ ∘ w = κ)
        (fun w => alt (κ ∘ w + rhoV n))
      rw [mul_smul_comm, mul_add, mul_smul_comm, alt_orbit, e1, ← e3, ← hS, e2]
      simp [smul_smul, hc]
  intro κ hκ
  obtain ⟨k, hk⟩ := dM_nat (κ ∘ (1 : Equiv.Perm (Fin n)) + rhoV n) (hint κ hκ 1)
  have hk' : dM (κ + rhoV n) = k := hk
  exact main (k + 1) κ hκ (by rw [hk']; exact_mod_cast Nat.lt_succ_self k)
