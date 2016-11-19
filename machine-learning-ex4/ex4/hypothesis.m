function h = hypothesis(Theta1, Theta2, X)
  m = size(X, 1);
  num_labels = size(Theta2, 1);

  p = zeros(size(X, 1), 1);

  h1 = sigmoid([ones(m, 1) X] * Theta1');
  h = sigmoid([ones(m, 1) h1] * Theta2');
end
