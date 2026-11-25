module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.LatticeNormTransport

@[expose] public section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.SwFinM

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {n : ℕ}

theorem lattice_norm_matrix_conj (lam : Measure (Fin n → R)) [lam.IsAddHaarMeasure] (L : AddSubgroup (Fin n → R))
    (A Ai A' C B : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hAC : A' * C = 1) :
    PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (L.map (Matrix.mulVecLin A).toAddMonoidHom) (L.map (Matrix.mulVecLin C).toAddMonoidHom)
      (A * B * A') = PositivityTheory.SiegelWeilFormula.Gen.nu2 lam L L B := by
  have hL : (L.map (Matrix.mulVecLin C).toAddMonoidHom).map (Matrix.mulVecLin A').toAddMonoidHom = L := by
    rw [AddSubgroup.map_map]
    change L.map ((A'.mulVecLin.comp C.mulVecLin).toAddMonoidHom) = L
    rw [← Matrix.mulVecLin_mul, hAC, Matrix.mulVecLin_one]
    exact L.map_id
  simpa only [hL] using lattice_norm_matrix_transport lam L (L.map (Matrix.mulVecLin C).toAddMonoidHom) A Ai B A' h1 h2

end GlobalTheory.CompanionTheory.SwFinM
