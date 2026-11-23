module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
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

@[expose] public section

noncomputable section
open scoped Matrix Classical TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.Inhab
variable {D : D7}

section Generic

open Matrix Formalism.UG

variable {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) {n m k : Type}

variable [Fintype n] [Fintype m] [Fintype k] [DecidableEq n] [DecidableEq m] [DecidableEq k]

end Generic

section Lattice

variable {T T' : HSp D} {t : ℕ} (d : HypDec T T' t)

variable {L' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}

end Lattice

section Frame

variable {T T' : HSp D} {t : ℕ} (d : HypDec T T' t)

variable (c : Mx D T'.rank T'.rank)

end Frame

theorem exists_good (V : HSp D) : ∃ l : Lvl V, l.Good :=
  let ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj V
  ⟨⟨frameLat V, a⟩, isLattice_frameLat_host V, SelfDual.isSelfDualAt_frameLat D V, ha⟩

end GlobalTheory.RegSch.Inhab
