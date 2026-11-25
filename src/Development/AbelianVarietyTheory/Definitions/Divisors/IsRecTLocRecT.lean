module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace GlobalTheory.CuspRep.ParLawsT

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

def locRecT (hT : UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) : IrrGL (k := w.adicCompletion E) → WD h :=
  (hT E Ω A w h).choose

theorem isRecT_locRecT (hT : UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) :
    UpperTheory.Zero.LLC.IsRecT h (locRecT hT h) :=
  (hT E Ω A w h).choose_spec

variable [_root_.NumberField.IsTotallyComplex E]

def locParT (hT : UpperTheory.Zero.LLC.RecTExists) (π : CG E a) (h : IsPlaceOver A w) : WD h :=
  locRecT hT h ⟨a, ParLaws.toCl (π.loc w)⟩

end GlobalTheory.CuspRep.ParLawsT

namespace GlobalTheory.CuspRep.ParLawsT

open Formalism.BasicNotions



variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

def locGT (hT : UpperTheory.Zero.LLC.RecTExists) (pl : Formalism.GaloisCohomology.Places H.E Ω) {a : ℕ} (π : HostCGu H a) (w : PlE H) :
    WD (pl.2 w) :=
  haveI := host_isCMField H; locParT hT π.1 (pl.2 w)

end GlobalTheory.CuspRep.ParLawsT

end
