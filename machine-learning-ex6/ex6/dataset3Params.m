function [C, sigma] = dataset3Params(X, y, Xval, yval)
%EX6PARAMS returns your choice of C and sigma for Part 3 of the exercise
%where you select the optimal (C, sigma) learning parameters to use for SVM
%with RBF kernel
%   [C, sigma] = EX6PARAMS(X, y, Xval, yval) returns your choice of C and
%   sigma. You should complete this function to return the optimal C and
%   sigma based on a cross-validation set.
%

% You need to return the following variables correctly.
C = 1;
sigma = 0.3;

% ====================== YOUR CODE HERE ======================
% Instructions: Fill in this function to return the optimal C and sigma
%               learning parameters found using the cross validation set.
%               You can use svmPredict to predict the labels on the cross
%               validation set. For example,
%                   predictions = svmPredict(model, Xval);
%               will return the predictions on the cross validation set.
%
%  Note: You can compute the prediction error using
%        mean(double(predictions ~= yval))
%

C_candidates = [0.01; 0.03; 0.1; 0.3; 1; 3; 10; 30];
% C_candidates = [0.01];
sigma_candidates = C_candidates(:);

% cartesian product of C_candidates and sigma_candidates
[_x, _y] = meshgrid(C_candidates, sigma_candidates);
candidates = [_x(:) _y(:)];

num_candidates = size(candidates, 1);
errors         = zeros(num_candidates, 1);


for i = 1:num_candidates
  c   = candidates(i, 1);
  sig = candidates(i, 2);

  model = svmTrain(X, y, c, @(x1,x2) gaussianKernel(x1,x2,sig));
  predictions = svmPredict(model, Xval);
  errors(i) = mean(double(predictions ~= yval));
end

[_, i] = min(errors);

C     = candidates(i, 1);
sigma = candidates(i, 2);



% =========================================================================

end
