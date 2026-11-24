module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAddCharConjEqProdPlaceResidueCharsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeArgumentResidueEqWeightedSymmetricFrameSumStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricCharResidueConjEqWeightedUnipotentSumStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

theorem star_character_eq_prod_additive_characters_root : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ (ψ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (a : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → Fin D.R.r → (ZMod (D.host.g kv.1))ˣ), (∀ kv, ψ' kv ≠ 1) ∧ ∀ k ∈ X.K2, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) → star (X.chi2 k) = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ψ' kv (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a kv i j : ZMod (D.host.g kv.1)) * (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j else 0) :=
  by
  intro D X h hE hg
  obtain ⟨ψ', hψ, hchar⟩ := GlobalTheory.T.finiteAddChar_conj_eq_prod_placeResidueChars D X h hE hg
  refine ⟨ψ', fun kv i j => if GlobalTheory.Mem.SymChar.wtA D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j +
      GlobalTheory.Mem.SymChar.wtB D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j = 1 then 1 else -1, hψ, ?_⟩
  intro k hk Ns hM hU
  have hK : k ∈ X.B.I.Kset := hk.1
  rw [GlobalTheory.Mem.SymChar.otherInstanceCharacter_eq_psi_symmetricArgument, hchar _ _ _ (fun kv => GlobalTheory.T.heckeArgument_residue_eq_weighted_symmetricFrameSum D X h hE hg kv k hK _ (hM kv))
    (fun kv => GlobalTheory.T.symmetricCharResidue_conj_eq_weightedUnipotentSum D X h hE hg kv k hK (Ns kv) (hM kv) (hU kv))]
  refine Finset.prod_congr rfl fun kv _ => ?_
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases he : symEdge D.R.rS D.R.k i j
  · simp only [if_pos he]
    rw [← add_mul, ← Int.cast_add]
    rcases GlobalTheory.Mem.SymChar.wt_add D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j with h2 | h2
    · rw [h2]; simp
    · rw [h2]; simp
  · simp only [if_neg he, add_zero]

end GlobalTheory.Mem.SymChar
