module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

namespace GlobalTheory.LocFinComp

theorem prV_swap_snd {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (u : HeightOneSpectrum (𝓞 F)) (x : AF F ⊗[F] E) :
    Formalism.UG.prV (E := E) u (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x)) =
    Algebra.TensorProduct.comm F (Fv F u) E (Algebra.TensorProduct.map (evFin F u) (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => exact Eq.refl _
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem finE_locFin_map_prV_ne : ∀ {D : D7} (V : HSp D) {v u : HeightOneSpectrum (𝓞 D.host.F)}, u ≠ v → ∀ (g : Gv V v), (Formalism.IndefR.Lev.finE V (locFin V v g : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u) = 1 := by
  intro D V v u huv g
  have hp : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram u (locFin V v g : GA D V) = 1 :=
    GlobalTheory.AdelicU.proj_emb_ne D.sp.cm.sig V.gram huv g
  have hm := congrArg (fun y => (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram y).val) hp
  simp only [GlobalTheory.AdelicU.matHom_proj, map_one, Units.val_one] at hm
  ext i j
  have hij := congrFun (congrFun hm i) j
  have key := prV_swap_snd (F := D.host.F) (E := D.host.E) u
    ((Formalism.L2.Theta.matHom V (locFin V v g : GA D V)).val i j)
  refine key.trans ((congrArg (Algebra.TensorProduct.comm _ _ _) hij).trans ?_)
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

end GlobalTheory.LocFinComp
