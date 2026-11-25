module

public import Mathlib.Algebra.Algebra.Basic
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
open GlobalTheory.CuspMult

namespace GlobalTheory.LatLoc

theorem loc_transfer {R : Type} [CommRing R] {n : ℕ} {S : Subring R} (H₀ H₁ : Submodule S (Fin n → R)) (N : ℕ)
    (u : S) (ε : R) (hu : (u : R) * N = ε) (hε : ε * ε = ε) (h : ∀ y ∈ H₀, (N : R) • y ∈ H₁) (z : Fin n → R)
    (hz : (fun a => ε * z a) ∈ H₀) : (fun a => ε * z a) ∈ H₁ := by
  have h1 := H₁.smul_mem u (h _ hz)
  convert h1 using 1
  funext a
  show ε * z a = (u : R) * ((N : R) * (ε * z a))
  rw [← mul_assoc, hu, ← mul_assoc, hε]


end GlobalTheory.LatLoc
