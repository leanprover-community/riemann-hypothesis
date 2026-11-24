module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatticeSmulMemOfAgreeAwayFromPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem _root_.GlobalTheory.T.adelicLattice_smul_mem_of_agree_away_from_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (w : HeightOneSpectrum (𝓞 F)) (x x' : GL (Fin N) (AfE F E)), SameOff w x x' → ∃ m : ℕ, ∀ c : 𝓞 F, c ∈ w.asIdeal ^ m → ∀ y ∈ latAd x Lb, (algebraMap F E (c : F)) • y ∈ latAd x' Lb := by
  first | exact @GlobalTheory.TwV.Xc.latAd_smul_mem_of_sameOff | exact GlobalTheory.TwV.Xc.latAd_smul_mem_of_sameOff | (intros; apply GlobalTheory.TwV.Xc.latAd_smul_mem_of_sameOff <;> assumption)
