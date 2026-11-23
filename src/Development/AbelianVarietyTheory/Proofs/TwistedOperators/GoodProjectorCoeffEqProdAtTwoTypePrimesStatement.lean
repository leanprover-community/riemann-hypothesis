module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorCoeffEqProdAtTwoTypePrimes
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coeff_e0_eq_eGood_mul_eGood : ∀ (D : D7) (τ : ∀ k : Fin 2, (ZMod (D.host.g k))[X] → GlobalTheory.BadShare.GG (D.host.g k) D.R.r → ℂ), (∀ k, ∀ f ∈ GlobalTheory.BadShare.sqSet (D.host.g k) D.R.r, ∀ x, (D.ntypes.eSer k f).coeff x = GlobalTheory.BadShare.zc (τ k f) x) → ∀ γ : G0g D.nd, D.ntypes.e0.coeff γ = GlobalTheory.BadShare.eGood (fun _ => τ 0) (D.nd.chiT 0) (fun v => γ ⟨0, v⟩) * GlobalTheory.BadShare.eGood (fun _ => τ 1) (D.nd.chiT 1) (fun v => γ ⟨1, v⟩) := by
  first | exact @GlobalTheory.GoodProjProd.goodProjector_coeff_eq_prod_at_two_typePrimes | exact GlobalTheory.GoodProjProd.goodProjector_coeff_eq_prod_at_two_typePrimes | (intros; apply GlobalTheory.GoodProjProd.goodProjector_coeff_eq_prod_at_two_typePrimes <;> assumption)
