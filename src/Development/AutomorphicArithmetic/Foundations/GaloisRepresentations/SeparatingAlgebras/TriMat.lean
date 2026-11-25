module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt

@[expose] public section

open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.triMat_pf :
    UpperTheory.Gal.Gen.Flag → UpperTheory.Gal.Gen.TriMat := by
  intro hF l _ H _ hH X _ _ ρ
  let ρ' : Representation (ZMod l) H (X → ZMod l) :=
    ((Matrix.toLinAlgEquiv' (R := ZMod l) (n := X)).toAlgHom.toRingHom.toMonoidHom).comp
      (((Int.castRingHom (ZMod l)).mapMatrix (m := X)).toMonoidHom.comp ρ)
  have hρ' : ∀ h v, ρ' h v = ((ρ h).map (Int.castRingHom (ZMod l))).mulVec v := by
    intro h v
    rfl
  obtain ⟨b₀, hb₀⟩ := hF l H hH (X → ZMod l) ρ'
  have hcard : Module.finrank (ZMod l) (X → ZMod l) = Fintype.card X :=
    Module.finrank_fintype_fun_eq_card _
  let e : Fin (Module.finrank (ZMod l) (X → ZMod l)) ≃ Fin (Fintype.card X) := finCongr hcard
  let b := b₀.reindex e
  have hb : ∀ h i j, j ≤ i → b.repr (ρ' h (b j) - b j) i = 0 := by
    intro h i j hij
    have := hb₀ h (e.symm i) (e.symm j) (by simpa [e] using hij)
    simpa [b] using this
  let Q : Matrix (Fin (Fintype.card X)) X ℤ := fun i x => ((b.repr (Pi.single x 1) i).val : ℤ)
  let P : Matrix X (Fin (Fintype.card X)) ℤ := fun x j => ((b j x).val : ℤ)
  refine ⟨Q, P, fun h i j hij => ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1
  have hQ : Q.map (Int.castRingHom (ZMod l)) =
      LinearMap.toMatrix (Pi.basisFun (ZMod l) X) b LinearMap.id := by
    ext i x
    change (((b.repr (Pi.single x 1) i).val : ℤ) : ZMod l) = _
    rw [Int.cast_natCast, ZMod.natCast_zmod_val, LinearMap.toMatrix_apply,
      LinearMap.id_apply, Pi.basisFun_apply]
  have hP : P.map (Int.castRingHom (ZMod l)) =
      LinearMap.toMatrix b (Pi.basisFun (ZMod l) X) LinearMap.id := by
    ext x j
    change (((b j x).val : ℤ) : ZMod l) = _
    rw [Int.cast_natCast, ZMod.natCast_zmod_val, LinearMap.toMatrix_apply,
      LinearMap.id_apply, Pi.basisFun_repr]
  have hc : (((Q * ρ h * P) i j : ℤ) : ZMod l) = b.repr (ρ' h (b j)) i := by
    have h1 : (((Q * ρ h * P) i j : ℤ) : ZMod l) =
        ((Q * ρ h * P).map (Int.castRingHom (ZMod l))) i j := rfl
    rw [h1, Matrix.map_mul, Matrix.map_mul, hQ, hP,
      ← LinearMap.toMatrix_toLin (Pi.basisFun (ZMod l) X) (Pi.basisFun (ZMod l) X)
        ((ρ h).map (Int.castRingHom (ZMod l))),
      ← LinearMap.toMatrix_comp (Pi.basisFun (ZMod l) X) (Pi.basisFun (ZMod l) X) b,
      ← LinearMap.toMatrix_comp b (Pi.basisFun (ZMod l) X) b,
      LinearMap.id_comp, LinearMap.comp_id, LinearMap.toMatrix_apply,
      Matrix.toLin_eq_toLin', Matrix.toLin'_apply, ← hρ']
  have hd := hb h i j hij
  rw [map_sub, Finsupp.sub_apply, sub_eq_zero, Module.Basis.repr_self, Finsupp.single_apply] at hd
  rw [Int.cast_sub, hc, hd]
  by_cases hij' : i = j
  · subst hij'
    simp
  · simp [hij', Ne.symm hij']
