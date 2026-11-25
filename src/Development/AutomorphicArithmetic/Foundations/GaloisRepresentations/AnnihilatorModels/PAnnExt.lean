module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact

@[expose] public section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.annExt_of :
    DinvExt → AnnExt := by
  intro h F G B _ _ _ _ σ ψ L _ _ V _ _ ρ
  have hD := h F G B σ L V ρ
  have hinj : Function.Injective ((Dinv σ ρ).subtype.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Dinv σ ρ).injective_subtype
  refine ⟨fun e hadm => ?_, fun q n T hA x hx => ?_⟩
  · unfold admitted at hadm ⊢
    rw [← LinearEquiv.finrank_map_eq (AlgebraTensorModule.assoc F F L L V B), hD, Module.finrank_baseChange]
    rw [← hadm]
    change Module.finrank L (LinearMap.range ((Dinv σ ρ).subtype.baseChange L)) = _
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]
  · unfold AnnD at hA
    dsimp only
    have comm (f : V →ₗ[F] V) (g : B →ₗ[F] B) (y : (L ⊗[F] V) ⊗[F] B) :
        AlgebraTensorModule.assoc F F L L V B (AlgebraTensorModule.map (f.baseChange L) g y) =
          (AlgebraTensorModule.map f g).lTensor L (AlgebraTensorModule.assoc F F L L V B y) :=
      let F₁ : (L ⊗[F] V) ⊗[F] B →ₗ[F] L ⊗[F] (V ⊗[F] B) :=
        (AlgebraTensorModule.assoc F F L L V B).toLinearMap.restrictScalars F ∘ₗ
          (AlgebraTensorModule.map (f.baseChange L) g).restrictScalars F
      let F₂ : (L ⊗[F] V) ⊗[F] B →ₗ[F] L ⊗[F] (V ⊗[F] B) :=
        (AlgebraTensorModule.map f g).lTensor L ∘ₗ
          (AlgebraTensorModule.assoc F F L L V B).toLinearMap.restrictScalars F
      LinearMap.congr_fun (TensorProduct.ext' (g := F₁) (h := F₂) fun u b => LinearMap.congr_fun
        (TensorProduct.ext' (g := F₁ ∘ₗ (TensorProduct.mk F (L ⊗[F] V) B).flip b)
          (h := F₂ ∘ₗ (TensorProduct.mk F (L ⊗[F] V) B).flip b) fun a v => by simp [F₁, F₂]) u) y
    have hmem : AlgebraTensorModule.assoc F F L L V B x ∈ (Dinv σ ρ).baseChange L :=
      hD ▸ Submodule.mem_map_of_mem hx
    apply (AlgebraTensorModule.assoc F F L L V B).injective
    rw [map_sum, map_zero]; simp only [map_zsmul, comm]
    obtain ⟨z, hz⟩ := Submodule.toBaseChange_surjective' L (Dinv σ ρ) hmem
    rw [← hz]; clear hz hmem
    induction z using TensorProduct.inductionOn with
    | tmul a w =>
      simpa [Submodule.coe_toBaseChange_tmul, LinearMap.lTensor_tmul, map_sum, map_zsmul] using
        congrArg (TensorProduct.mk F L (V ⊗[F] B) a) (hA w w.2)
    | add z₁ z₂ h₁ h₂ =>
      simp only [map_add (f := _), Submodule.coe_add, Finset.sum_add_distrib,
        smul_add, h₁, h₂, add_zero]
