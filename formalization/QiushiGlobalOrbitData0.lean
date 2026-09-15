import QiushiGlobalOrbitNormalizer

namespace QiushiMatmul.GlobalOrbit.Cases0
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def free0 : List Nat := []

def rows0_0 : Array Transition := #[
  ⟨0, [], [0, 1, 2, 4, 8, 16, 32, 64, 128, 256], [2, 4, 8, 16, 32, 64, 128, 256, 512]⟩]

def blocks0 : Array (Array Transition) := #[rows0_0]

def rows0 (k : Fin (2 ^ free0.length)) : Transition :=
  ((blocks0.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free1 : List Nat := [8]

def rows1_0 : Array Transition := #[
  ⟨1, [], [0, 1, 2, 4, 8, 16, 32, 64, 128], [2, 4, 8, 16, 32, 64, 128, 256]⟩,
  ⟨0, [], [1, 2, 4, 8, 16, 32, 64, 128, 256], [1, 2, 4, 8, 16, 32, 64, 128, 256]⟩]

def blocks1 : Array (Array Transition) := #[rows1_0]

def rows1 (k : Fin (2 ^ free1.length)) : Transition :=
  ((blocks1.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free2 : List Nat := [5]

def rows2_0 : Array Transition := #[
  ⟨2, [], [0, 1, 2, 4, 8, 16, 32, 64, 128], [2, 4, 8, 16, 32, 64, 128, 256]⟩,
  ⟨0, [], [8, 1, 10, 4, 16, 32, 64, 128, 256], [2, 5, 8, 1, 16, 32, 64, 128, 256]⟩]

def blocks2 : Array (Array Transition) := #[rows2_0]

def rows2 (k : Fin (2 ^ free2.length)) : Transition :=
  ((blocks2.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free3 : List Nat := [2]

def rows3_0 : Array Transition := #[
  ⟨3, [], [0, 1, 2, 4, 8, 16, 32, 64, 128], [2, 4, 8, 16, 32, 64, 128, 256]⟩,
  ⟨0, [], [64, 1, 2, 68, 8, 80, 32, 128, 256], [2, 4, 9, 16, 33, 64, 1, 128, 256]⟩]

def blocks3 : Array (Array Transition) := #[rows3_0]

def rows3 (k : Fin (2 ^ free3.length)) : Transition :=
  ((blocks3.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free4 : List Nat := [7, 8]

def rows4_0 : Array Transition := #[
  ⟨4, [], [0, 1, 2, 4, 8, 16, 32, 64], [2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨1, [], [1, 2, 4, 8, 16, 32, 64, 128], [1, 2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨1, [3, 1], [4, 32, 8, 1, 64, 16, 2, 128], [8, 64, 1, 4, 32, 2, 16, 128]⟩,
  ⟨1, [3, 0, 1, 2, 0, 1], [32, 4, 65, 1, 8, 130, 2, 16], [8, 64, 2, 16, 128, 1, 12, 96]⟩]

def blocks4 : Array (Array Transition) := #[rows4_0]

def rows4 (k : Fin (2 ^ free4.length)) : Transition :=
  ((blocks4.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free5 : List Nat := [5, 8]

def rows5_0 : Array Transition := #[
  ⟨5, [], [0, 1, 2, 4, 8, 16, 32, 64], [2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨1, [], [4, 5, 2, 8, 16, 32, 64, 128], [3, 4, 1, 8, 16, 32, 64, 128]⟩,
  ⟨2, [], [1, 2, 4, 8, 16, 32, 64, 128], [1, 2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨2, [0, 1, 2, 1, 0], [1, 10, 20, 8, 16, 32, 64, 128], [1, 10, 20, 8, 16, 32, 64, 128]⟩]

def blocks5 : Array (Array Transition) := #[rows5_0]

def rows5 (k : Fin (2 ^ free5.length)) : Transition :=
  ((blocks5.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free6 : List Nat := [5, 7]

def rows6_0 : Array Transition := #[
  ⟨6, [], [0, 1, 2, 4, 8, 16, 32, 64], [2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨1, [3, 1], [8, 4, 32, 1, 64, 16, 2, 128], [8, 64, 2, 1, 32, 4, 16, 128]⟩,
  ⟨1, [1], [8, 4, 16, 1, 2, 32, 64, 128], [8, 16, 2, 1, 4, 32, 64, 128]⟩,
  ⟨2, [], [2, 1, 4, 8, 16, 32, 64, 128], [2, 1, 4, 8, 16, 32, 64, 128]⟩]

def blocks6 : Array (Array Transition) := #[rows6_0]

def rows6 (k : Fin (2 ^ free6.length)) : Transition :=
  ((blocks6.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free7 : List Nat := [5, 7]

def rows7_0 : Array Transition := #[
  ⟨7, [], [0, 1, 2, 4, 8, 16, 32, 64], [2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨1, [3, 1], [8, 4, 40, 1, 64, 16, 2, 128], [8, 64, 2, 1, 32, 5, 16, 128]⟩,
  ⟨2, [3, 0], [32, 1, 2, 64, 8, 4, 128, 16], [2, 4, 32, 16, 128, 1, 8, 64]⟩,
  ⟨2, [3, 2, 0], [34, 1, 2, 72, 8, 4, 144, 16], [2, 4, 32, 16, 128, 5, 24, 192]⟩]

def blocks7 : Array (Array Transition) := #[rows7_0]

def rows7 (k : Fin (2 ^ free7.length)) : Transition :=
  ((blocks7.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free8 : List Nat := [4, 5]

def rows8_0 : Array Transition := #[
  ⟨8, [], [0, 1, 2, 4, 8, 16, 32, 64], [2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨2, [0, 1, 2, 1, 0], [8, 9, 10, 20, 16, 32, 64, 128], [3, 5, 24, 1, 16, 32, 64, 128]⟩,
  ⟨2, [1], [1, 3, 9, 16, 4, 32, 64, 128], [1, 3, 16, 5, 8, 32, 64, 128]⟩,
  ⟨2, [0, 1, 0, 2, 0, 1, 0], [11, 10, 3, 4, 20, 32, 64, 128], [3, 7, 8, 5, 24, 32, 64, 128]⟩]

def blocks8 : Array (Array Transition) := #[rows8_0]

def rows8 (k : Fin (2 ^ free8.length)) : Transition :=
  ((blocks8.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free9 : List Nat := [4, 5]

def rows9_0 : Array Transition := #[
  ⟨9, [], [0, 1, 2, 4, 8, 16, 32, 64], [2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨2, [], [8, 1, 2, 12, 16, 32, 64, 128], [2, 4, 9, 1, 16, 32, 64, 128]⟩,
  ⟨2, [3, 1, 0], [64, 32, 65, 2, 8, 128, 4, 16], [5, 8, 64, 16, 128, 2, 1, 32]⟩,
  ⟨2, [1, 3, 2, 0, 1, 2, 0], [33, 72, 42, 3, 1, 144, 20, 4], [16, 24, 128, 13, 192, 17, 15, 224]⟩]

def blocks9 : Array (Array Transition) := #[rows9_0]

def rows9 (k : Fin (2 ^ free9.length)) : Transition :=
  ((blocks9.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free10 : List Nat := [2, 5]

def rows10_0 : Array Transition := #[
  ⟨10, [], [0, 1, 2, 4, 8, 16, 32, 64], [2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨2, [], [32, 1, 2, 36, 8, 16, 64, 128], [2, 4, 9, 16, 32, 1, 64, 128]⟩,
  ⟨2, [0, 3, 0], [4, 1, 36, 2, 128, 16, 64, 8], [2, 8, 1, 128, 32, 5, 64, 16]⟩,
  ⟨2, [2, 0, 3, 2, 0], [4, 1, 38, 2, 216, 24, 72, 8], [2, 8, 1, 128, 160, 13, 192, 240]⟩]

def blocks10 : Array (Array Transition) := #[rows10_0]

def rows10 (k : Fin (2 ^ free10.length)) : Transition :=
  ((blocks10.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free11 : List Nat := [2, 8]

def rows11_0 : Array Transition := #[
  ⟨11, [], [0, 1, 2, 4, 8, 16, 32, 64], [2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨1, [], [32, 1, 34, 4, 40, 16, 64, 128], [2, 5, 8, 17, 32, 1, 64, 128]⟩,
  ⟨3, [], [1, 2, 4, 8, 16, 32, 64, 128], [1, 2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨3, [1, 2, 1], [1, 66, 132, 8, 16, 32, 64, 128], [1, 66, 132, 8, 16, 32, 64, 128]⟩]

def blocks11 : Array (Array Transition) := #[rows11_0]

def rows11 (k : Fin (2 ^ free11.length)) : Transition :=
  ((blocks11.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free12 : List Nat := [2, 6]

def rows12_0 : Array Transition := #[
  ⟨12, [], [0, 1, 2, 4, 8, 16, 32, 64], [2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨1, [3, 0, 1], [16, 4, 32, 8, 80, 1, 128, 2], [32, 128, 2, 8, 1, 4, 17, 64]⟩,
  ⟨2, [1, 0], [128, 32, 64, 1, 2, 4, 8, 16], [8, 16, 32, 64, 128, 2, 4, 1]⟩,
  ⟨3, [], [4, 1, 2, 8, 16, 32, 64, 128], [2, 4, 1, 8, 16, 32, 64, 128]⟩]

def blocks12 : Array (Array Transition) := #[rows12_0]

def rows12 (k : Fin (2 ^ free12.length)) : Transition :=
  ((blocks12.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free13 : List Nat := [2, 5]

def rows13_0 : Array Transition := #[
  ⟨13, [], [0, 1, 2, 4, 8, 16, 32, 64], [2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨2, [], [32, 1, 2, 36, 40, 16, 64, 128], [2, 4, 9, 17, 32, 1, 64, 128]⟩,
  ⟨3, [], [8, 1, 10, 4, 16, 32, 64, 128], [2, 5, 8, 1, 16, 32, 64, 128]⟩,
  ⟨3, [2, 3, 2], [2, 1, 14, 4, 244, 192, 160, 128], [2, 1, 8, 13, 248, 192, 160, 128]⟩]

def blocks13 : Array (Array Transition) := #[rows13_0]

def rows13 (k : Fin (2 ^ free13.length)) : Transition :=
  ((blocks13.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free14 : List Nat := [2, 5]

def rows14_0 : Array Transition := #[
  ⟨14, [], [0, 1, 2, 4, 8, 16, 32, 64], [2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨2, [3, 0], [4, 1, 32, 2, 68, 8, 128, 16], [2, 8, 1, 32, 128, 4, 17, 64]⟩,
  ⟨2, [1, 0], [1, 32, 64, 129, 2, 4, 8, 16], [1, 16, 32, 64, 128, 2, 4, 9]⟩,
  ⟨3, [2], [8, 1, 2, 12, 80, 160, 64, 128], [2, 4, 9, 1, 80, 160, 64, 128]⟩]

def blocks14 : Array (Array Transition) := #[rows14_0]

def rows14 (k : Fin (2 ^ free14.length)) : Transition :=
  ((blocks14.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)

def free15 : List Nat := [2, 4]

def rows15_0 : Array Transition := #[
  ⟨15, [], [0, 1, 2, 4, 8, 16, 32, 64], [2, 4, 8, 16, 32, 64, 128]⟩,
  ⟨2, [3, 1, 0], [128, 32, 1, 130, 64, 8, 4, 16], [4, 9, 64, 32, 128, 2, 16, 1]⟩,
  ⟨2, [0, 3, 0], [128, 1, 32, 130, 4, 16, 64, 8], [2, 9, 16, 128, 32, 4, 64, 1]⟩,
  ⟨2, [1, 0], [2, 32, 64, 130, 1, 4, 8, 16], [16, 1, 32, 64, 128, 2, 4, 9]⟩]

def blocks15 : Array (Array Transition) := #[rows15_0]

def rows15 (k : Fin (2 ^ free15.length)) : Transition :=
  ((blocks15.getD (k.val / 64) #[]).getD (k.val % 64) ⟨0, [], [], []⟩)


end QiushiMatmul.GlobalOrbit.Cases0
