module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.Prism GlobalTheory.BKReal
open scoped NNReal

namespace GlobalTheory.BSP.Height

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}
  {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {τ : Ainf l} {s : Seed bk d ρ τ} (ht : Height s)

def bas : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := s.X.map (toDisc l (X : bk.S) bk.ρ₀) * ht.Z

def Rel {B : Obj l ↥(OL K)} (u : B.A) (f g : Hom bk.prism B)
    (ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀)) : Prop :=
  ∀ Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf f) Ff → IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) Fg →
    toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (ht.bas.map Ff * ε) =
      toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • ht.bas.map Fg

theorem rel_one {B : Obj l ↥(OL K)} (u : B.A) (f : Hom bk.prism B) : ht.Rel u f f 1 := fun Ff Fg hf hg => by
  rw [hf.unique hg, mul_one]

end GlobalTheory.BSP.Height
