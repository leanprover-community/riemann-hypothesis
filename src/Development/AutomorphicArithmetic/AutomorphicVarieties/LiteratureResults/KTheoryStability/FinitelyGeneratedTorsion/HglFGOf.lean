module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.FinitelyGeneratedTorsion.TensTorsion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Assembly
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ColsMinSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ImportsAlt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open CategoryTheory NumberField

namespace UpperTheory.FiniteGenerationAndTorsion

open UpperTheory.V UpperTheory.V.KH

theorem hglFG_of (h : FgShift) : HglFG := by
  intro L _ _ hL N m
  have := hL
  let C := faceCx (KT.Gm L N) (KT.Sx L N) (KT.Sx.face L N) KT.Sx.face_smul
  have hx := KT.sx_exact L N m
  exact h (KT.Gm L N) (KT.orbBound L N m) (3 ^ (KT.dd L N * N)) m (KT.Sx L N)
    (fun p => Rep.ofHom ⟨C.d p, fun g => LinearMap.ext fun f => C.d_equiv p g f⟩)
    (Rep.trivial ℤ (KT.Gm L N) ℤ)
    (Rep.ofHom ⟨C.ε, fun g => LinearMap.ext fun f => C.ε_equiv g f⟩)
    (Nat.one_le_pow _ _ (by norm_num)) hx.1 hx.2.1 hx.2.2
    (fun p hp => ⟨(KT.orb L N p).1, (KT.orb L N p).2.trans (KT.orbBound_mono L N hp)⟩)
    (fun p _ => KT.stab L N p)

end UpperTheory.FiniteGenerationAndTorsion

end
