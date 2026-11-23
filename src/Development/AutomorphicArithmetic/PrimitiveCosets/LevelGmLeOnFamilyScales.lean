module

public import Development.AutomorphicArithmetic.PrimitiveCosets.WindowInequalityOfArtinInputs
public import Formalism.SharpRestriction.GlobalSchurBounds.TieGlobal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
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

namespace UpperTheory.Comparison₂

open Formalism.HC Formalism.MainNotions Formalism.BasicNotions

theorem tiedCore_of_chainTied {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ) (h : ChainTied Fm eD eL K cHH eK CL x) :
    FamCoreConstantBounds Fm.toFamCore eD eL K cHH eK x := by
  obtain ⟨i0, m, f, pt, av, bv, Top, iT, Dd, C, Xpp, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    -, -, -, ⟨tT, t2, -, -, hell⟩, h1, h2, h3, h4, h5, h7, h8, h9, h10, ⟨⟨s1, s2, s3, s4, s5, s6, ⟨n1, n2, n3⟩, s8⟩, th, -⟩, h12, h13⟩ := h
  have hTT : TT = (Fm.D x i0).host.TT := by
    ext t
    rw [tT t, ← Fm.TT_eq x i0, Finset.mem_image]
    exact ⟨fun ⟨s, hs, e⟩ => (Frame.A.val_injective _ e) ▸ hs, fun ht => ⟨t, ht, rfl⟩⟩
  subst hTT
  refine ⟨i0, _, inferInstance, id, fun u0 => (Fm.D x (pt u0)).what₂.Word, fun _ => inferInstance, fun _ => inferInstance, Top, iT,
    m, f, Dd, C, Xpp, ell, N, T2, a, w, eT, eP, η, X', θ, hell, h1, h2, h3, h4, h5, fun s _ => ⟨s, rfl⟩, h7, h8, h9, h10,
    ⟨s1, s2, s3, s4, s5, s6, fun u _ => n1 u, fun u _ => n2 u, fun u _ => n3 u, fun u _ => s8 u⟩, th, h12, h13, fun s hs => ?_⟩
  obtain ⟨k, -, rfl⟩ := (t2 0 s).1 hs
  exact Frame.digit_mem_cyclic_subgroup _ k

theorem level_gm_le_on_family_scales (Λ : Level) :
    ChebyshevInequalityOnWindows (Fam := FamP) (fun Fm => Fm.toFamCore) (fun Fm => ChainTied Fm) Λ :=
  windowInequality_of_artinInputs (fun Fm => tiedCore_of_chainTied Fm) Λ

end UpperTheory.Comparison₂

end
