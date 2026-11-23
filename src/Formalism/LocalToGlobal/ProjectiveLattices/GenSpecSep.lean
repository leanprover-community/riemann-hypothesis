module

public import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem sepX (Xo : Moduli Dw l) : SepXSt Xo := by
  unfold SepXSt
  have hq := Xo.qproj
  unfold IsQProjOver at hq
  obtain ⟨N, i, hi, -, hcomp⟩ := hq
  rw [← hcomp]
  haveI := hi
  infer_instance

theorem spMap_isDominant {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (hφ : Function.Injective φ) :
    IsDominant (spMap φ) := by
  unfold spMap
  constructor
  have hd : DenseRange (PrimeSpectrum.comap φ) := by
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact hd

theorem x_eq_of_inj (Xo : Moduli Dw l) {S T : Type} [CommRing S] [IsReduced S] [CommRing T] (φ : S →+* T)
    (hφ : Function.Injective φ) {f g : Sp S ⟶ Xo.X} (hs : f ≫ Xo.s = g ≫ Xo.s)
    (h : spMap φ ≫ f = spMap φ ≫ g) : f = g := by
  haveI : IsSeparated Xo.s := sepX Xo
  haveI : IsDominant (spMap φ) := spMap_isDominant φ hφ
  first
  | exact ext_of_isDominant_of_isSeparated Xo.s hs (spMap φ) h
  | exact ext_of_isDominant_of_isSeparated Xo.s hs h
  | exact ext_of_isDominant_of_isSeparated (s := Xo.s) hs (ι := spMap φ) h

end Formalism.L2.Pj
