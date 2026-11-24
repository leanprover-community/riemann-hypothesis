module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTuple
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

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure SStage (B : Base) (C : Cols B) (W : RowsRest B C) where
  dsig : (Tau B.R) → ℝ
  dsig_pos : ∀ ρ, 0 < dsig ρ
  s : Formalism.MainNotions.S.Draft.SData B.R B.host.F B.host.E B.toPre.conjF B.Word (Tau B.R) B.hcW
  s_split : ∀ p, (s.atP p).split.isSome ↔
    Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  s_HH : Module.finrank ℂ s.HH = W.Dall
  s_Cu : ∀ u, s.Cu u ≃ₗ[ℂ] (C.mem u).A.Mu0
  s_PlF : s.PlF ≃ HeightOneSpectrum (𝓞 B.host.F)
  s_Cu_isom : ∀ u (x y : s.Cu u), inner ℂ x y =
    (C.fm u).ipC 0 ((s_Cu u x : (C.mem u).A.Mu0) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)
      ((s_Cu u y : (C.mem u).A.Mu0) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)
  sEE : W.EE →ₗᵢ⋆[ℂ] s.HH

end GlobalTheory.Mem

end
