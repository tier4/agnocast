#include <memory>

namespace agnocast
{

class Node
{
public:
  using SharedPtr = std::shared_ptr<Node>;
};

}  // namespace agnocast