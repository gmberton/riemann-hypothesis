module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
open UpperTheory.Gal.TP.Sub

private theorem sumRep_entry {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r : Γ →* GL (Fin a) k)
    (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  have hi : finSumFinEquiv.symm (Fin.castAdd b i) = Sum.inl i := finSumFinEquiv_symm_apply_castAdd i
  have hj : finSumFinEquiv.symm (Fin.castAdd b j) = Sum.inl j := finSumFinEquiv_symm_apply_castAdd j
  simp [sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
  rfl

theorem UpperTheory.Gal.TP.Sub.contLeft_holds :
    ContLeft := by
  intro Γ k _ _ _ _ _ _ a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s hc
    refine Continuous.of_coeHom_comp (f := r) ?_
    change Continuous fun g => (r g : Matrix (Fin a) (Fin a) k)
    have hm : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) :=
      Units.continuous_val.comp hc
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have he : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k)
        (Fin.castAdd b i) (Fin.castAdd b j) :=
      (continuous_apply _).comp ((continuous_apply _).comp hm)
    exact he.congr fun g => sumRep_entry r s g i j
  · rintro r r' ⟨u, hu⟩ hr
    have hf : (⇑r') = fun x => u * r x * u⁻¹ := funext hu
    rw [hf]
    exact (continuous_const.mul hr).mul continuous_const
  · intro r c hr hc
    refine Continuous.of_coeHom_comp (f := tw r c) ?_
    change Continuous fun g => ((tw r c g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
    have hv : (fun g => ((tw r c g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)) =
        fun g => ((c g : kˣ) : k) • (r g : Matrix (Fin a) (Fin a) k) :=
      funext fun g => UpperTheory.V.Af.tw_val r c g
    rw [hv]
    exact (Units.continuous_val.comp hc).smul (Units.continuous_val.comp hr)
  · intro c hc
    refine Continuous.of_coeHom_comp (f := rk1 c) ?_
    change Continuous fun g => ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)
    have hv : (fun g => ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) =
        fun g => Matrix.diagonal fun _ => ((c g : kˣ) : k) := by
      funext g
      simp [rk1, Matrix.scalar_apply]
    rw [hv]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val.comp hc)
