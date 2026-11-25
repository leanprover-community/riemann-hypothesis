module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TestFnCusp

theorem hypH_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (h : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ := by
  intro a ha har
  obtain ⟨v, hv⟩ := h.2 a ha har
  refine ⟨v, fun y hy => hv y fun g hg => hy g ?_⟩
  intro i j hij
  by_contra hc
  exact hij (hg i j hc)

theorem isCuspidalOp_tensor : (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ (tensor D.sp.cm.sig V.gram fa ff) := by
  intro hCO hPC D V lam S M T U μa μf μ _ _ fa ff hTD
  obtain ⟨hodd, -, -, hnf, hμ, ha, hb⟩ := hTD
  haveI : ∀ w, (μa w).IsHaarMeasure := hμ.haar_arch
  haveI : ∀ v, (μf v).IsHaarMeasure := hμ.haar_loc
  have hT : IsTestFnG M T U μa μf (tensor D.sp.cm.sig V.gram fa ff) := ⟨fa, ff, ha, hb, rfl⟩
  have hf : tensor D.sp.cm.sig V.gram fa ff ∈ CcGA V := hT.isPureTensor.2
  have hU := hPC.2 D V hodd S M T (hypH_of_noFixed T hnf) U μa μf _ hT
  refine hCO D V μ _ hf ?_ ?_
  · intro 𝔉 h𝔉 ν hν x y
    exact ((hU 𝔉 h𝔉).1 ν x y).2
  · intro 𝔉 h𝔉 ν hν x y
    exact ((hU 𝔉 h𝔉).2 ν x y).2

end GlobalTheory.TestFnCusp

end
