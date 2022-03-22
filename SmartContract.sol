// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.4.16 <0.8.4;
contract LoRaWAN{
    event newDataAdded(uint256 _tx_index, string _cid,   string _timestamp);
    struct SensorData{
        uint256 tx_index;
        string cid;
        string url;
        string timestamp;
        bytes signature;
        bytes public_key;
    }
    mapping(string => SensorData) Data;
    string[] public SensorDataList;
    function newData(
        uint256  _tx_index,
        string memory _cid,
        string memory _url,
        string memory _timestamp,
        bytes memory _signature,
        bytes memory _public_key) 
        public{
            Data[_cid].cid = _cid;
            Data[_cid].url = _url;
            Data[_cid].timestamp = _timestamp;
            Data[_cid].signature = _signature;
            Data[_cid].public_key = _public_key;
        SensorDataList.push(_cid);
        emit newDataAdded(_tx_index, _cid, _timestamp);
    }
    function countTx() view public returns(uint){
        return SensorDataList.length;
    }
    function getData(string memory _cid)
        view
        public
        returns(uint256, string memory, string memory, string memory,  bytes memory, bytes memory)
        {
            return(
            Data[_cid].tx_index, 
            Data[_cid].cid,
            Data[_cid].url,
            Data[_cid].timestamp,
            Data[_cid].signature,
            Data[_cid].public_key);
        }
}