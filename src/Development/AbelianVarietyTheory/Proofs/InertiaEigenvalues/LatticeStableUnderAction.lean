module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriangularMul
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum



namespace GlobalTheory.LatKeep

variable {D : D7}

theorem intGL_mulVec_int {n : ℕ} (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (v : Fin n → EAf D)
    (hv : ∀ i, v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (i : Fin n) :
    (((Formalism.L2.DIV.intGL D.host.F D.host.E n y : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ v) i ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
  simp only [Matrix.mulVec, dotProduct]
  refine sum_mem fun j _ => mul_mem ?_ (hv j)
  exact (y.val i j).2

theorem isFrame_mul_intGL {n : ℕ} {β : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    Formalism.L2.DIV.IsFrame (β * Formalism.L2.DIV.intGL D.host.F D.host.E n y) Λ := by
  intro x
  rw [hβ x]
  have e1 : (((β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x
      = ((Formalism.L2.DIV.intGL D.host.F D.host.E n y⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ
          (((β⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x) := by
    have hm : (β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ = Formalism.L2.DIV.intGL D.host.F D.host.E n y⁻¹ * β⁻¹ := by
      rw [_root_.mul_inv_rev, MonoidHom.map_inv]
    rw [hm, Units.val_mul, Matrix.mulVec_mulVec]
  have e2 : ((β⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x
      = ((Formalism.L2.DIV.intGL D.host.F D.host.E n y : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ
          ((((β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x) := by
    rw [e1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  constructor
  · intro h i
    rw [e1]
    exact intGL_mulVec_int _ _ h i
  · intro h i
    rw [e2]
    exact intGL_mulVec_int _ _ h i

end GlobalTheory.LatKeep
