module Lesson13.Undestroyable

export -- But not public.
data UndT = UndV

export
mkUnd : UndT
mkUnd = UndV

export
dropUnd : (1 _: UndT) -> ()
dropUnd UndV = ()

export
mkUndF : (1 _ : (1 _ : UndT) -> a) -> a
mkUndF f = f UndV

export
mkUndIO : (1 _ : (1 _ : UndT) -> IO ()) -> IO ()
mkUndIO f = f UndV
