module

public import Formalism.RankGapBounds.TheoremALocOfLemmaA
public import Formalism.SatakeDualWeyl.DualWeylRepApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.RankGapBounds.CloudMinFalse

@[expose] public section

open MvPolynomial TensorProduct

noncomputable section

namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla

open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA

def UnitsOfLocal : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (l : ℕ), l.Prime → ¬ IsUnit (l : O) →
    ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : O)

def deltaIn (O : Type) [CommRing O] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) :
    Submodule O (dualWeyl O r n ν) :=
  (weyl O r n hn ν).comap (dualWeyl O r n ν).subtype

abbrev Nabla (O : Type) [CommRing O] {ι : Type} (r n : ι → ℕ) (ν : ∀ i, Fin (n i) → ℕ) : Type :=
  ⨂[O] i, ↥(dualWeyl O (r i) (n i) (ν i))

def Delta (O : Type) [CommRing O] {ι : Type} (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
    (ν : ∀ i, Fin (n i) → ℕ) : Submodule O (Nabla O r n ν) :=
  tensSub fun i => deltaIn O (r i) (n i) (hn i) (ν i)

def nablaRep (O : Type) [CommRing O] {ι : Type} (r n : ι → ℕ) (ν : ∀ i, Fin (n i) → ℕ) :
    Representation O (∀ i, Matrix.GeneralLinearGroup (Fin (r i)) O) (Nabla O r n ν) :=
  PiTensorProduct.mapMonoidHom.comp
    (MonoidHom.pi fun i => (dualWeylRep O (r i) (n i) (ν i)).comp (Pi.evalMonoidHom _ i))

def NablaRepTprod : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) (r n : ι → ℕ) (ν : ∀ i, Fin (n i) → ℕ)
    (g : ∀ i, Matrix.GeneralLinearGroup (Fin (r i)) O)
    (a : ∀ i, ↥(dualWeyl O (r i) (n i) (ν i))),
    nablaRep O r n ν g (PiTensorProduct.tprod O a) =
      PiTensorProduct.tprod O (fun i => dualWeylRep O (r i) (n i) (ν i) (g i) (a i)) ∧
    ∀ i, ((dualWeylRep O (r i) (n i) (ν i) (g i) (a i) : ↥(dualWeyl O (r i) (n i) (ν i))) :
      MvPolynomial (Fin (r i) × Fin (n i)) O) = dwAct O (r i) (n i) (g i) (a i)

def DeltaInStable : Prop :=
  ∀ (O : Type) [CommRing O] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ)
    (g : Matrix.GeneralLinearGroup (Fin r) O), ∀ x ∈ deltaIn O r n hn ν,
    dualWeylRep O r n ν g x ∈ deltaIn O r n hn ν

end Formalism.CohomologicalDescent.RealLocalDeltaNabla
