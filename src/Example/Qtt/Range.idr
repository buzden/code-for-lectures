module Example.Qtt.Range

fromMaybe : (1 _ : Maybe a) -> a -> a
fromMaybe (Just x) _ = x
fromMaybe Nothing  d = d
