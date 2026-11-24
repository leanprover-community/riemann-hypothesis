module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDetRoot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteIdeleCharAtDeterminantRoots
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormOneTwist

variable {D : D7}

def quotC (D : D7) : (AE D)ˣ →* (AE D)ˣ :=
  MonoidHom.id _ / Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

def finQuot (D : D7) : (AE D)ˣ →* (GlobalTheory.FinalJoin.AfE D)ˣ :=
  (Units.map (finPart D).toMonoidHom).comp (quotC D)

theorem finPart_mul_inv (x : (AE D)ˣ) :
    finPart D (x : AE D) * finPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
  rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]

theorem finQuot_val (x : (AE D)ˣ) :
    ((finQuot D x : (GlobalTheory.FinalJoin.AfE D)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      finPart D (x : AE D) * sigR (Af D.host.F) D.sp.cm.sig (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) := by
  show finPart D ((x : AE D) * sigR (AF D.host.F) D.sp.cm.sig ((x⁻¹ : (AE D)ˣ) : AE D)) = _
  rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR]

theorem normOne_finQuot (x : (AE D)ˣ) : GlobalTheory.FinalJoin.NormOne (finQuot D x) := by
  change _ * sigR (Af D.host.F) D.sp.cm.sig _ = 1
  rw [finQuot_val]
  exact GlobalTheory.DetOnto.norm_one _ (GlobalTheory.DetOnto.sigR_sigR D) (finPart_mul_inv x)

theorem finQuot_of_isDetRoot {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hx : IsDetRoot V g x) :
    finQuot D x = Matrix.GeneralLinearGroup.det (finHom V g) := by
  apply Units.ext
  have h1 := congrArg (finPart D) hx
  rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR] at h1
  rw [finQuot_val, h1, mul_assoc, ← RingHom.map_mul, finPart_mul_inv x, RingHom.map_one, mul_one,
    GlobalTheory.DetRootChar.finPart_det]

theorem finQuot_incA (e : D.host.Eˣ) :
    ((finQuot D (Units.map (incA D).toMonoidHom e) : (GlobalTheory.FinalJoin.AfE D)ˣ) : GlobalTheory.FinalJoin.AfE D) =
      (1 : Af D.host.F) ⊗ₜ[D.host.F] ((e : D.host.E) * D.sp.cm.sig ((e⁻¹ : D.host.Eˣ) : D.host.E)) := by
  rw [finQuot_val]
  show finPart D (incA D (e : D.host.E)) * sigR (Af D.host.F) D.sp.cm.sig (finPart D (incA D ((e⁻¹ : D.host.Eˣ) : D.host.E))) = _
  show ((1 : Af D.host.F) ⊗ₜ[D.host.F] (e : D.host.E)) *
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] D.sp.cm.sig ((e⁻¹ : D.host.Eˣ) : D.host.E)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end GlobalTheory.NormOneTwist

namespace GlobalTheory.NormOneTwist

variable {D : D7}

end GlobalTheory.NormOneTwist
