module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.T

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem norm_gal (v : HeightOneSpectrum (𝓞 F)) (σ : E ≃ₐ[F] E)
    (w u : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    [u.asIdeal.LiesOver v.asIdeal] (h : u = σ • w) (y : w.adicCompletion E) :
    ‖galEquiv v σ w u h y‖ = ‖y‖ := by
  subst h
  exact (HeightOneSpectrum.denseRange_algebraMap E w).induction_on y
    (isClosed_eq (continuous_norm.comp (continuous_galEquiv v σ w _ rfl)) continuous_norm)
    fun x => by rw [galEquiv_algebraMap, norm_algebraMap_smul]

private theorem galFin_eq_piGal (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (y : CompletionsOver E v) : galFin σ v y = piGal v σ y := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  have h1 : galFin σ v (tensorEquiv' E v t) =
      tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E)
        (AlgHom.id F (v.adicCompletion F)) t) := by
    simp [galFin, galOf]
  have h2 : ∀ z, tensorEquiv' E v z = tensorEquiv E v (Algebra.TensorProduct.comm F E _ z) :=
    congrFun (tensorMap'_eq_comp E v)
  have h3 : (Algebra.TensorProduct.map (AlgHom.id F (v.adicCompletion F)) (σ : E →ₐ[F] E) :
      v.adicCompletion F ⊗[F] E → _) =
      Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion F) _) (σ : E →ₐ[F] E) :=
    congrArg DFunLike.coe (Algebra.TensorProduct.ext' fun _ _ => rfl :
      Algebra.TensorProduct.map (AlgHom.id F _) (σ : E →ₐ[F] E) =
        (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion F) _)
          (σ : E →ₐ[F] E)).restrictScalars F)
  rw [h1, h2, h2, Algebra.TensorProduct.comm_comp_map_apply, h3, tensorEquiv_map_gal]

variable {w u : HeightOneSpectrum (𝓞 E)} (φ : w.adicCompletion E →+* u.adicCompletion E)

private theorem le_of_norm (hφ : ∀ y, ‖φ y‖ = ‖y‖) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y ≤ 1) : valuation (u.adicCompletion E) (φ y) ≤ 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).le_one_iff_le_one,
    ← Valued.toNormedField.norm_le_one_iff, hφ, Valued.toNormedField.norm_le_one_iff]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).le_one_iff_le_one.1 hy

private theorem lt_of_norm (hφ : ∀ y, ‖φ y‖ = ‖y‖) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y < 1) : valuation (u.adicCompletion E) (φ y) < 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).lt_one_iff_lt_one,
    ← Valued.toNormedField.norm_lt_one_iff, hφ, Valued.toNormedField.norm_lt_one_iff]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).lt_one_iff_lt_one.1 hy

private theorem eq_of_norm (hφ : ∀ y, ‖φ y‖ = ‖y‖) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y = 1) : valuation (u.adicCompletion E) (φ y) = 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).eq_one_iff_eq_one,
    ← Valued.toNormedField.norm_eq_one_iff, hφ, Valued.toNormedField.norm_eq_one_iff]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one.1 hy

private theorem integral_map (n : ℕ) (hφ : ∀ y, ‖φ y‖ = ‖y‖)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLnLocal.integralGL (w.adicCompletion E) n) :
    mapGL n φ g ∈ GLnLocal.integralGL (u.adicCompletion E) n := by
  rw [GLnLocal.mem_integralGL_iff] at hg ⊢
  rw [← map_inv]
  simp only [Valuation.mem_integer_iff] at hg ⊢
  exact ⟨fun i j => le_of_norm φ hφ (hg.1 i j), fun i j => le_of_norm φ hφ (hg.2 i j)⟩

private theorem iwahori_map (n : ℕ) (hφ : ∀ y, ‖φ y‖ = ‖y‖)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLnLocal.iwahori (w.adicCompletion E) n) :
    mapGL n φ g ∈ GLnLocal.iwahori (u.adicCompletion E) n := by
  rw [GLnLocal.mem_iwahori_iff] at hg ⊢
  exact ⟨fun i j => le_of_norm φ hφ (hg.1 i j), fun i j h => lt_of_norm φ hφ (hg.2.1 i j h),
    fun i => eq_of_norm φ hφ (hg.2.2 i)⟩

end

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.offStable :
    UpperTheory.ConvolutionTheory.T.OffStable := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v
  have hv : ∀ (u : PlacesOver E v) y,
      ‖(galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u)).toRingEquiv.toRingHom y‖ = ‖y‖ :=
    fun u y => UpperTheory.ConvolutionTheory.T.norm_gal v σ _ _ _ y
  have hc : ∀ (x : GL (Fin n) (CompletionsOver E v)) (u : PlacesOver E v),
      GM.cmp u (mapGL n (galFin σ v) x) =
        mapGL n (galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u)).toRingEquiv.toRingHom
          (GM.cmp (σ⁻¹ • u) x) :=
    fun x u => Units.ext (Matrix.ext fun a b =>
      congrFun (UpperTheory.ConvolutionTheory.T.galFin_eq_piGal σ v _) u)
  refine ⟨fun x hx u => ?_, fun x hx u => ?_,
    ⟨⨅ u : PlacesOver E v, (GLnLocal.integralGL (u.1.adicCompletion E) n).comap (GM.cmp u), ?_⟩,
    ⟨⨅ u : PlacesOver E v, (GLnLocal.iwahori (u.1.adicCompletion E) n).comap (GM.cmp u),
      fun g => by simp [Subgroup.mem_iInf]⟩,
    fun w => ⟨And.intro (GLnLocal.isCompact_integralGL _ n) (GLnLocal.isOpen_integralGL _ n),
      And.intro (GLnLocal.isCompact_iwahori _ n) (GLnLocal.isOpen_iwahori _ n),
      GLnLocal.iwahori_le_integralGL _ n⟩⟩
  · rw [hc]
    exact UpperTheory.ConvolutionTheory.T.integral_map _ n (hv u) (hx _)
  · rw [hc]
    exact UpperTheory.ConvolutionTheory.T.iwahori_map _ n (hv u) (hx _)
  · ext g
    simp [unitSet, GM.cmp]
