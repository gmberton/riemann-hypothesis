module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem alt_expand {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] {d q : ℕ} (f : M [⋀^Fin q]→ₗ[R] N) (a : Fin q → Fin d → R) (v : Fin d → M) :
    f (fun i => ∑ l, a i l • v l) =
      ∑ S : {S : Finset (Fin d) // S.card = q},
        (Matrix.of fun i j => a i (S.1.orderEmbOfFin S.2 j)).det •
          f (fun j => v (S.1.orderEmbOfFin S.2 j)) := by
  classical
  let b := Pi.basisFun R (Fin d)
  let φ : (Fin d → R) [⋀^Fin q]→ₗ[R] N := f.compLinearMap (Fintype.linearCombination R v)
  let ψ : ExteriorAlgebra R (Fin d → R) →ₗ[R] N :=
    ExteriorAlgebra.liftAlternating fun k => if h : k = q then h ▸ φ else 0
  have hx := congrArg (fun z : ⋀[R]^q (Fin d → R) => ψ z)
    ((b.exteriorPower q).sum_repr (exteriorPower.ιMulti R q a))
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    exteriorPower.ιMulti_apply_coe] at hx
  have h1 : ψ (ExteriorAlgebra.ιMulti R q a) = f (fun i => ∑ l, a i l • v l) := by
    simp [ψ, φ, Fintype.linearCombination_apply]
  rw [← h1, ← hx]
  let e : Set.powersetCard (Fin d) q ≃ {S : Finset (Fin d) // S.card = q} :=
    ⟨fun s => ⟨s.1, s.2⟩, fun s => ⟨s.1, s.2⟩, fun _ => rfl, fun _ => rfl⟩
  refine Fintype.sum_equiv e _ _ fun s => congrArg₂ (· • ·) ?_ ?_
  · rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    simp [Module.Basis.coord_apply, Pi.basisFun_repr, b, e,
      Set.powersetCard.ofFinEmbEquiv_symm_apply]
  · simp [ψ, φ, exteriorPower.basis_apply, ExteriorAlgebra.ιMulti_family, b, e,
      Fintype.linearCombination_apply_single, Set.powersetCard.ofFinEmbEquiv_symm_apply]

private theorem mapDR_iM (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] (n : ℕ) (v : Fin n → K) :
    mapDR ℂ K L (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (v a)) =
      ExteriorAlgebra.ιMulti L n fun a => D ℂ L (algebraMap K L (v a)) := by
  simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext a
  simp [mapDR, map1, KaehlerDifferential.map_D]

private theorem pullback_kahler_iMulti {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] (j2 : K →ₐ[ℂ] L)
    (n : ℕ) (v : Fin n → K) :
    pr2L j2 (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (v a)) =
      ExteriorAlgebra.ιMulti L n fun a => D ℂ L (j2 (v a)) := by
  letI : Algebra K L := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_iM K L n v

private theorem iM_cast {L : Type} [Field L] [Algebra ℂ L] {d : ℕ} (S : Finset (Fin d)) (q : ℕ)
    (h : S.card = q) (w : Fin d → Ω[L⁄ℂ]) :
    ExteriorAlgebra.ιMulti L q (fun j => w (S.orderEmbOfFin h j)) =
      ExteriorAlgebra.ιMulti L S.card (fun j => w (S.orderEmbOfFin rfl j)) := by
  subst h; rfl

theorem UpperTheory.Gal.productCup_of_system.dtPull_of :
    LocOne → ValBasic → DtPull := by
  intro hLO hVB F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY e he T
  refine ⟨?_, ?_⟩
  · refine (mapDR_iM K K' _ _).trans ?_
    unfold dtS
    congr 1
    funext a
    rw [tt, tt, IsScalarTower.algebraMap_apply F K K']
  · obtain ⟨hle, ⟨ev, hev⟩, hbv, -⟩ := hVB K' (rB ℂ K' (xv x) {0}) e.1
    have hLoc := hLO F K' d x hY.covY hY.red e
    have htB : ∀ l, tt K' x l ∈ rB ℂ K' (xv x) {0} := fun l => tco_mem ℂ K' (xv x) l
    have ht0 : ∀ l, ev ⟨tt K' x l, hle (htB l)⟩ = 0 := fun l => by
      obtain ⟨h, hh⟩ := (hev _ _).1 (hbv ⟨tt K' x l, htB l⟩)
      exact hh.trans (e.2 l)
    choose g hgv hgt using hY.tan e he
    have hg : ∀ m l, ∃ h : g m l ∈ loc (rB ℂ K' (xv x) {0}) e.1, ev ⟨g m l, h⟩ = A e m l :=
      fun m l => (hev _ _).1 (hgv m l)
    choose hgl hge using hg
    choose c hcl hcD using fun m l => hLoc (g m l) (hgl m l)
    let ah : Matrix (Fin d) (Fin d) (loc (rB ℂ K' (xv x) {0}) e.1) := fun m l =>
      ⟨g m l, hgl m l⟩ + ∑ l', ⟨tt K' x l', hle (htB l')⟩ * ⟨c m l' l, hcl m l' l⟩
    have hah : ∀ m l, (ah m l : K') = g m l + ∑ l', tt K' x l' * c m l' l := fun m l => by
      simp [ah]
    have hAh : ev.mapMatrix ah = A e := by
      ext m l
      change ev (⟨g m l, hgl m l⟩ + ∑ l', ⟨tt K' x l', hle (htB l')⟩ * ⟨c m l' l, hcl m l' l⟩) = A e m l

      rw [map_add (f := _), map_sum, hge]
      simp only [map_mul, ht0, zero_mul, Finset.sum_const_zero, add_zero]
    have hD : ∀ m, D ℂ K' (j2 (tt K x m)) = ∑ l, (ah m l : K') • D ℂ K' (tt K' x l) := by
      intro m

      rw [hgt m, map_sum]
      simp_rw [hah, add_smul, Finset.sum_add_distrib, Derivation.leibniz, hcD, Finset.smul_sum,
        Finset.sum_smul, smul_smul]
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm
    refine ⟨fun S => if hS : S.card = T.card then
      (((ah.submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin hS)).det :
        loc (rB ℂ K' (xv x) {0}) e.1) : K') else 0, ?_, ?_⟩
    · have h1 : pr2L j2 (dtS K x T) = ExteriorAlgebra.ιMulti K' T.card (fun a =>
          ∑ l, (ah (T.orderEmbOfFin rfl a) l : K') • D ℂ K' (tt K' x l)) := by
        unfold dtS
        rw [pullback_kahler_iMulti]
        congr 1
        funext a
        exact hD _
      rw [h1, alt_expand (ExteriorAlgebra.ιMulti K' T.card)
        (fun a l => (ah (T.orderEmbOfFin rfl a) l : K')) (fun l => D ℂ K' (tt K' x l)),
        Finset.sum_subtype (Finset.univ.powersetCard T.card) (p := fun S => S.card = T.card)
          (by simp [Finset.mem_powersetCard])]
      refine Finset.sum_congr rfl fun S _ => ?_
      simp only [dite_eq_left S.2]
      rw [iM_cast S.1 T.card S.2 (fun l => D ℂ K' (tt K' x l))]
      unfold dtS
      congr 1
      exact ((loc (rB ℂ K' (xv x) {0}) e.1).val.map_det
        (ah.submatrix (T.orderEmbOfFin rfl) (S.1.orderEmbOfFin S.2))).symm
    · intro S hS
      simp only [dite_eq_left hS]
      refine (hev _ _).2 ⟨SetLike.coe_mem _, ?_⟩
      change ev (ah.submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin hS)).det = _
      rw [AlgHom.map_det, ← hAh]
      rfl
