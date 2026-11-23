module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseLift

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyBadModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def keyInOf {R : Type} [CommRing R] (t : SAB H (Sp R)) (th : t.PP.L.Sec) (g : ℕ) (hg : 1 ≤ g)
    (v : Fin g → (epsR R ⟶ t.G)) (hv : IsLieBasis v) (hab : IsAbelianScheme t.G)
    (hd : SmoothOfRelativeDimension g t.G.hom) (hs : Out.Sym t.G t.PP.L) (ha : Out.RelAmple t.G t.PP.L)
    (hk : Out.KTriv t.G t.PP.L) (hth : ∀ s : Sp R, ∃ x : t.G.left, t.G.hom x = s ∧ x ∈ Out.nonzeroLocus th) : KeyIn R where
  P := { A := t.G, isAb := hab, g := g, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB,
         rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := hs, ample := ha, ktriv := hk }
  g_pos := hg
  rig := t.PP.rig
  rig_gen := t.PP.rigGen
  th := th
  th_ne := hth
  v := v
  basis := hv

end GlobalTheory.CompanionTheory.Ar.Sl.KeyBadModel
