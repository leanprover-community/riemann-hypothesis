module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace Ysupp

def SubEmbedding : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible →
      ∃ (c : ℕ) (x : Fin c → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ a, (x a).IsCusp) ∧
        ∃ φ : π.IntertwiningMap (prodIrr x hd), Function.Injective φ

end Ysupp
