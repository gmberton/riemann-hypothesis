module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocB
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKur
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial

@[expose] public section

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.ValGroupKprime

theorem norm_Kunr (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] {c : Om l} (hc : c ∈ Kunr l a) (h0 : c ≠ 0) :
    ∃ m : ℤ, ‖c‖ = (l : ℝ) ^ m := by
  have hK : MaximalUnramifiedExtension l ≤ ReciprocityTheory.ChartRestriction.L1.kurAlg l := by
    refine IntermediateField.adjoin_le_iff.2 fun x ⟨m, hm, hlm, hx⟩ => ?_
    refine ReciprocityTheory.ChartRestriction.L1.mem_kurAlg.2
      (Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨m, hm, hlm, ?_⟩))
    rw [← map_pow, hx, map_one]
  have h1 := ReciprocityTheory.ChartRestriction.L1.mem_kurAlg.1 (hK (Kunr_le_Kur l a hc))
  obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.L1.kur_val l h1 ((map_ne_zero _).2 h0)
  exact ⟨m, by rw [← hm]; exact (PadicComplex.norm_extends l c).symm⟩

theorem norm_natCast_l (l : ℕ) [Fact l.Prime] : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [Padic.norm_p] at this
  simpa using this

theorem norm_pow_field (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (y : Om l) (hy : y ∈ (ϖ.field a).1) (h0 : y ≠ 0) : ∃ j : ℤ, ‖y‖ ^ e = (l : ℝ) ^ j := by
  set π := ϖ.seq 0 with hπdef
  set E := Kunr l a with hE
  have hπ0 : π ≠ 0 := ϖ.seq_ne_zero 0

  have hy' : y ∈ IntermediateField.adjoin E {π} := by
    have h1 : (ϖ.field a).1 = (IntermediateField.adjoin E {π}).restrictScalars ℚ_[l] := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]; rfl
    rw [h1] at hy; exact hy
  have hint : IsAlgebraic E π :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) π).tower_top.isAlgebraic
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint] at hy'

  let M : Submodule E (Om l) := Submodule.span E (Set.range fun i : Fin e => π ^ (i : ℕ))
  have hlE : (-(l : Om l)) ∈ E := E.neg_mem (IntermediateField.natCast_mem E l)
  have hpow : ∀ n, π ^ n ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < e
      · exact Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hn)
        have hk : k < e + k := by have := NeZero.pos e; omega
        have h2 : π ^ (e + k) = (⟨-(l : Om l), hlE⟩ : E) • π ^ k := by
          rw [pow_add, ϖ.seq_zero]; rfl
        rw [h2]; exact M.smul_mem _ (ih k hk)
  have hyM : y ∈ M := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
    obtain ⟨p, rfl⟩ := hy'
    show Polynomial.aeval π p ∈ M
    rw [Polynomial.aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun i _ => M.smul_mem _ (hpow i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hyM
  set t : Fin e → Om l := fun i => (c i : Om l) * π ^ (i : ℕ) with ht
  have hyt : y = ∑ i, t i := by rw [← hc]; rfl

  have hnπ : ‖π‖ ^ e = (l : ℝ)⁻¹ := by
    rw [← norm_pow, ϖ.seq_zero, norm_neg, norm_natCast_l]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith

  have hnt : ∀ i, t i ≠ 0 → ∃ m : ℤ, ‖t i‖ ^ e = (l : ℝ) ^ ((e : ℤ) * m - (i : ℕ)) := by
    intro i hi
    have hci : (c i : Om l) ≠ 0 := fun h => hi (by simp [ht, h])
    obtain ⟨m, hm⟩ := norm_Kunr l a (c i).2 hci
    refine ⟨m, ?_⟩
    rw [ht]; dsimp only
    rw [norm_mul, norm_pow, mul_pow, hm, ← pow_mul, mul_comm (i : ℕ) e, pow_mul, hnπ,
      zpow_sub₀ hl0.ne', inv_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm m, zpow_natCast, div_eq_mul_inv]

  have hdist : ∀ i j, t i ≠ 0 → t j ≠ 0 → ‖t i‖ = ‖t j‖ → i = j := by
    intro i j hi hj hij
    obtain ⟨m1, h1⟩ := hnt i hi
    obtain ⟨m2, h2⟩ := hnt j hj
    have h3 : (e : ℤ) * m1 - (i : ℕ) = (e : ℤ) * m2 - (j : ℕ) :=
      zpow_right_injective₀ hl0 hl1.ne' (show (l : ℝ) ^ _ = (l : ℝ) ^ _ by rw [← h1, ← h2, hij])
    have h4 : ((i : ℕ) : ℤ) - (j : ℕ) = 0 := by
      have hi' := i.2
      have hj' := j.2
      refine Int.eq_zero_of_abs_lt_dvd (m := (e : ℤ)) ⟨m1 - m2, by linear_combination -h3⟩ ?_
      rw [abs_lt]; constructor <;> omega
    exact Fin.ext (by omega)

  classical
  set s := Finset.univ.filter (fun i => t i ≠ 0) with hs
  obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 := by
    by_contra! h
    exact h0 (hyt.trans (Finset.sum_eq_zero fun j _ => h j))
  have hsne : s.Nonempty := ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  have hsum : y = ∑ j ∈ s, t j := by
    rw [hyt, hs, Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => by split_ifs with hj; rfl; exact not_not.1 hj
  have hpw : Set.Pairwise (s : Set (Fin e)) (fun a b => ‖t a‖ ≠ ‖t b‖) := fun a ha b hb hab h =>
    hab (hdist a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2 h)
  obtain ⟨i0, hi0, hi0s⟩ := s.exists_mem_eq_sup' hsne (fun a => ‖t a‖)
  obtain ⟨m, hm⟩ := hnt i0 (Finset.mem_filter.1 hi0).2
  exact ⟨_, by
    rw [hsum, IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne hsne hpw, hi0s, hm]⟩

end GlobalTheory.ValGroupKprime
