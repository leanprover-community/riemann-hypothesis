module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

theorem exField_of_keyFin_exKey : KeyFin → ExKey → ExField := by
  classical
  intro h2 h1
  obtain ⟨c, h1⟩ := h1
  refine ⟨c, fun ε CF hC => ?_⟩
  obtain ⟨x, h1⟩ := h1 ε CF hC
  refine ⟨x, fun s e hx P f Ξ hΞ => ?_⟩
  obtain ⟨𝒦, hK, H⟩ := h2 P Ξ hΞ
  choose S hS HS using h1 s e hx P f
  refine ⟨hK.toFinset.biUnion S, fun z hz => ?_, fun Y f' hP hf large₂ hs Γ _ _ Pl0 U A Ks _ _ _ R F st hC ho hc hz => ?_⟩
  · obtain ⟨κ, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS κ z hz
  · obtain ⟨κ, hκ, hk⟩ := H Y U R.toLevCh A.μ0 hP st.core.lev hc
    exact HS κ Y f' hP hf large₂ hs Γ Pl0 U A Ks R F st hC ho hk fun z hz' =>
      hz z (Finset.mem_biUnion.2 ⟨κ, hK.mem_toFinset.2 hκ, hz'⟩)

end GlobalTheory.RowEx

end
