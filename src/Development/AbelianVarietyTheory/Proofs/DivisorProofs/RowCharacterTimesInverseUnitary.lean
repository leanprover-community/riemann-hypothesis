module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataExtra

@[expose] public section

open NumberField

noncomputable section

namespace GlobalTheory.CovTop

open Formalism.L2.DIV

theorem prod_hom_pow_eq_one {H M ι : Type} [Group H] [CommMonoid M] (s : Finset ι) (f : ι → H →* M) (N : ℕ)
    (h : ∀ i x, f i x ^ N = 1) (x : H) : (∏ i ∈ s, f i) x ^ N = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have ih' : (∏ i ∈ s, f i x) ^ N = 1 := by simpa using ih
    simp [hi, mul_pow, h, ih']

theorem ofLocal_chi_pow {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    (Hl : (PP : Pg) → Subgroup (GL (Fin r) (kP PP.1))) (cl : (PP : Pg) → Hl PP →* LLˣ) (N : ℕ)
    (h : ∀ PP x, cl PP x ^ N = 1) (g : (LevelP.ofLocal Hl cl).H) : (LevelP.ofLocal Hl cl).chi g ^ N = 1 :=
  prod_hom_pow_eq_one (H := Subgroup.pi Set.univ Hl) Finset.univ _ N (fun PP x => h PP _) g

theorem unipotentTypeLevel_char_pow_eq_one {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : (PP : Pl E) → AddChar (kP PP) LL) (N : ℕ) (hN : ∀ PP : Pg, (N : kP PP.1) = 0)
    (g : (P0 Pg r ψ).H) : (P0 Pg r ψ).chi g ^ N = 1 := by
  refine ofLocal_chi_pow _ _ N (fun PP x => ?_) g
  apply Units.ext
  simp only [addCharHom, Units.val_pow_eq_pow_val, MonoidHom.coe_toHomUnits, Units.val_one, MonoidHom.comp_apply,
    AddChar.toMonoidHom_apply]
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hN PP, zero_mul, AddChar.map_zero_eq_one]

theorem det_of_mem_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    Matrix.det_of_upperTriangular (fun i j hij => hg.1 hij)]
  exact Finset.prod_eq_one fun i _ => hg.2 i

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

end GlobalTheory.CovTop
