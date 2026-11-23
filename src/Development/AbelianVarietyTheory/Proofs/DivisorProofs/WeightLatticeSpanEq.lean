module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanks
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.GenShift

open IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}

theorem exists_twPow (s : TwSec U x Z (wtOf Dw 0 1)) : ∀ n : ℕ, Nonempty (TwSec U x Z (wtOf Dw 0 (n : ℤ))) := by
  intro n
  induction n with
  | zero => exact ⟨(TwSec.const x s.pts 1 one_ne_zero).copy (by rw [Nat.cast_zero, wtOf_zero])⟩
  | succ n ih =>
    obtain ⟨t⟩ := ih
    exact ⟨(t.mul s).copy (by rw [← wtOf_add, add_zero, Nat.cast_succ])⟩


set_option maxHeartbeats 1000000 in
theorem span_latW_add (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G G₀ : WTZ E) (hG : Even G.2)
    (hs : ∀ Z : Comp Xo c, Nonempty (TwSec U x Z G₀))
    (h : Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) = ⊤) :
    Submodule.span c.F (latW U (G + G₀) : Set (cuspW Xo c U (G + G₀))) = ⊤ := by
  classical
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [eq_top_iff]
  intro F _
  have hF : F = ∑ Z : Comp Xo c,
      (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U (G + G₀)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (sum_idem_mul _).symm
  rw [hF]
  refine Submodule.sum_mem _ fun Z _ => ?_
  obtain ⟨s⟩ := hs Z
  obtain ⟨φ, -, -, hA, -⟩ := GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, -⟩ := GlobalTheory.FlatTw.Good.exists_twist_scalar s
  let p : cuspOn U Z (G + G₀) := ⟨idem Z * (F : Rul Xo c),
    GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2, by rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)⟩
  let g : cuspOn U Z G := φ.symm p
  have hmem : (⟨(g : Rul Xo c), g.2.1⟩ : cuspW Xo c U G) ∈ Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) := by
    rw [h]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 c.F)) c.F _ _ hmem
  rw [Submodule.span_eq, Submonoid.smul_def, ← algebraMap_smul c.F] at ht
  set d : c.F := algebraMap (𝓞 c.F) c.F t with hd
  have hd0 : d ≠ 0 := by simpa [hd] using nonZeroDivisors.ne_zero t.2
  have hf : d • g ∈ latOn U Z G := (mem_latOn U).2 ht
  have hq := hA a ha0 hlo (d • g) hf ((a * d) • p) (by
    simp only [g, map_smul, LinearEquiv.apply_symm_apply, Submodule.coe_smul, smul_smul])
  have hq' := (mem_latOn U).1 hq
  have had : a * d ≠ 0 := mul_ne_zero ha0 hd0
  have e : (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U (G + G₀)) =
      (a * d)⁻¹ • (⟨(((a * d) • p : cuspOn U Z (G + G₀)) : Rul Xo c), ((a * d) • p).2.1⟩ : cuspW Xo c U (G + G₀)) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, smul_smul, inv_mul_cancel₀ had, one_smul, p]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hq')

end General

end GlobalTheory.GenShift
