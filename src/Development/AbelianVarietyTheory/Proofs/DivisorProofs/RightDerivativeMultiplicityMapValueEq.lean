module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsUnitaryRepStableConjSkewAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSobolevContinuousOrbitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.MultDer

theorem smoothVec_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : SmoothVec L π 0 := by
  intro k Xs _
  simp only [map_zero]
  exact contDiff_const

theorem smoothVec_of_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {w : M.H τ} (hw : w ∈ M.sm τ) : SmoothVec (lieAt V τ) (M.rep τ) w := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact smoothVec_zero _ _
  | add x y _ _ hx hy =>
    intro k Xs h
    simp only [map_add (f := _)]
    exact (hx k Xs h).add (hy k Xs h)
  | smul c x _ hx =>
    intro k Xs h
    simp only [map_smul]
    exact (hx k Xs h).const_smul c

end GlobalTheory.HolRead.MultDer
